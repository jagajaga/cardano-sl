{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

-- To support actual wallet accounts we listen to applications and rollbacks
-- of blocks, extract transactions from block and extract our
-- accounts (such accounts which we can decrypt).
-- We synchronise wallet-db (acidic-state) with node-db
-- and support last seen tip for each walletset.
-- There are severals cases when we must  synchronise wallet-db and node-db:
-- • When we relaunch wallet. Desynchronization can be caused by interruption
--   during blocks application/rollback at the previous launch,
--   then wallet-db can fall behind from node-db (when interruption during rollback)
--   or vice versa (when interruption during application)
--   @syncWSetsWithGStateLock@ implements this functionality.
-- • When a user wants to import a secret key. Then we must rely on
--   Utxo (GStateDB), because blockchain can be large.

module Pos.Wallet.Web.Tracking.Sync
       ( syncWalletsWithGState
       , syncWalletOnImport
       , BlockLockMode
       , WalletTrackingSyncEnv

       , trackingApplyTxs
       , trackingApplyTxToModifierM
       , trackingRollbackTxs

       -- For tests
       , evalChange
       ) where

import           Universum
import           Unsafe (unsafeLast)

import           Control.Lens (to)
import           Control.Monad.Catch (handleAll)
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M
import           Ether.Internal (HasLens (..))
import           Formatting (build, sformat, (%))
import           System.Wlog (HasLoggerName, WithLogger, logInfo, modifyLoggerName)

import           Pos.Block.Types (Blund, undoTx)
import           Pos.Client.Txp.History (TxHistoryEntry (..))
import           Pos.Core (BlockHeaderStub, ChainDifficulty, HasConfiguration, HasDifficulty (..),
                           HeaderHash, SlotId, Timestamp, blkSecurityParam, genesisHash, headerHash,
                           headerSlotL)
import           Pos.Core.Block (BlockHeader, getBlockHeader, mainBlockTxPayload)
import           Pos.Core.Txp (TxAux (..), TxOutAux (..), TxUndo, toaOut, txOutAddress)
import           Pos.Crypto (EncryptedSecretKey, WithHash (..), shortHashF, withHash)
import           Pos.DB.Block (getBlund)
import qualified Pos.DB.Block.Load as GS
import qualified Pos.DB.BlockIndex as DB
import           Pos.DB.Class (MonadDBRead (..))
import qualified Pos.DB.Class as DB
import qualified Pos.GState as GS
import           Pos.GState.BlockExtra (foldlUpWhileM, resolveForwardLink)
import           Pos.Slotting (MonadSlots (..), getSlotStartPure, getSystemStartM)
import           Pos.StateLock (Priority (..), StateLock, withStateLockNoMetrics)
import           Pos.Txp (flattenTxPayload, genesisUtxo, unGenesisUtxo, utxoToModifier, _txOutputs)
import           Pos.Util.Chrono (getNewestFirst)
import           Pos.Util.LogSafe (logInfoS, logWarningS)
import qualified Pos.Util.Modifier as MM
import           Pos.Util.Util (getKeys)

import           Pos.Wallet.Web.Account (AccountMode, getSKById)
import           Pos.Wallet.Web.ClientTypes (Addr, CId, CWAddressMeta (..), Wal, addrMetaToAccount,
                                             encToCId)
import           Pos.Wallet.Web.Error.Types (WalletError (..))
import           Pos.Wallet.Web.Pending.Types (PtxBlockInfo)
import           Pos.Wallet.Web.State (MonadWalletDB, WalletTip (..))
import qualified Pos.Wallet.Web.State as WS
import           Pos.Wallet.Web.Tracking.Decrypt (THEntryExtra (..), WalletDecrCredentials,
                                                  buildTHEntryExtra, eskToWalletDecrCredentials,
                                                  isTxEntryInteresting, selectOwnAddresses)
import           Pos.Wallet.Web.Tracking.Modifier (VoidModifier, WalletModifier (..),
                                                   deleteAndInsertIMM, deleteAndInsertMM,
                                                   deleteAndInsertVM, emmDelete, emmInsert)

type BlockLockMode ctx m =
     ( WithLogger m
     , MonadDBRead m
     , MonadReader ctx m
     , HasLens StateLock ctx StateLock
     , MonadMask m
     )

type WalletTrackingSyncEnv ctx m =
     ( MonadWalletDB ctx m
     , MonadSlots ctx m
     , BlockLockMode ctx m
     )

syncWalletOnImport :: WalletTrackingSyncEnv ctx m => EncryptedSecretKey -> m ()
syncWalletOnImport = syncWalletsWithGState . one

----------------------------------------------------------------------------
-- Logic
----------------------------------------------------------------------------

-- Iterate over blocks (using forward links) and actualize our accounts.
syncWalletsWithGState
    :: forall ctx m . WalletTrackingSyncEnv ctx m
    => [EncryptedSecretKey] -> m ()
syncWalletsWithGState encSKs = forM_ encSKs $ \encSK -> handleAll (onErr encSK) $ do
    let wAddr = encToCId encSK
    WS.getWalletSyncTip wAddr >>= \case
        Nothing                -> logWarningS $ sformat ("There is no syncTip corresponding to wallet #"%build) wAddr
        Just NotSynced         -> syncDo encSK Nothing
        Just (SyncedWith wTip) -> DB.getHeader wTip >>= \case
            Nothing ->
                throwM $ InternalError $
                    sformat ("Couldn't get block header of wallet by last synced hh: "%build) wTip
            Just wHeader -> syncDo encSK (Just wHeader)
  where
    onErr encSK = logWarningS . sformat fmt (encToCId encSK)
    fmt = "Sync of wallet "%build%" failed: "%build

    syncDo :: EncryptedSecretKey -> Maybe BlockHeader -> m ()
    syncDo encSK wTipH = do
        let wdiff = maybe (0::Word32) (fromIntegral . ( ^. difficultyL)) wTipH
        gstateTipH <- DB.getTipHeader
        -- If account's syncTip is before the current gstate's tip,
        -- then it loads accounts and addresses starting with @wHeader@.
        -- syncTip can be before gstate's the current tip
        -- when we call @syncWalletSetWithTip@ at the first time
        -- or if the application was interrupted during rollback.
        -- We don't load all blocks explicitly, because blockain can be long.
        wNewTip <-
            if (gstateTipH ^. difficultyL > fromIntegral blkSecurityParam + fromIntegral wdiff) then do
                -- Wallet tip is "far" from gState tip,
                -- rollback can't occur more then @blkSecurityParam@ blocks,
                -- so we can sync wallet and GState without the block lock
                -- to avoid blocking of blocks verification/application.
                bh <- unsafeLast . getNewestFirst <$> GS.loadHeadersByDepth (blkSecurityParam + 1) (headerHash gstateTipH)
                logInfo $
                    sformat ("Wallet's tip is far from GState tip. Syncing with "%build%" without the block lock")
                    (headerHash bh)
                syncWalletWithGStateUnsafe encSK wTipH bh
                pure $ Just bh
            else pure wTipH
        withStateLockNoMetrics HighPriority $ \tip -> do
            logInfo $ sformat ("Syncing wallet with "%build%" under the block lock") tip
            tipH <- maybe (error "No block header corresponding to tip") pure =<< DB.getHeader tip
            syncWalletWithGStateUnsafe encSK wNewTip tipH

----------------------------------------------------------------------------
-- Unsafe operations. Core logic.
----------------------------------------------------------------------------
-- These operation aren't atomic and don't take the block lock.

-- BE CAREFUL! This function iterates over blockchain, the blockchain can be large.
syncWalletWithGStateUnsafe
    :: forall ctx m .
    ( MonadWalletDB ctx m
    , MonadDBRead m
    , WithLogger m
    , MonadSlots ctx m
    , HasConfiguration
    )
    => EncryptedSecretKey      -- ^ Secret key for decoding our addresses
    -> Maybe BlockHeader       -- ^ Block header corresponding to wallet's tip.
                               --   Nothing when wallet's tip is genesisHash
    -> BlockHeader             -- ^ GState header hash
    -> m ()
syncWalletWithGStateUnsafe encSK wTipHeader gstateH = setLogger $ do
    systemStart  <- getSystemStartM
    slottingData <- GS.getSlottingData
    curSlot <- getCurrentSlotInaccurate

    let gstateHHash = headerHash gstateH
        loadCond (b, _) _ = b ^. difficultyL <= gstateH ^. difficultyL
        wAddr = encToCId encSK
        mappendR r mm = pure (r <> mm)
        diff = (^. difficultyL)
        mDiff = Just . diff
        gbTxs = either (const []) (^. mainBlockTxPayload . to flattenTxPayload)

        mainBlkHeaderTs mBlkH =
            getSlotStartPure systemStart (mBlkH ^. headerSlotL) slottingData
        blkHeaderTs = either (const Nothing) mainBlkHeaderTs

        -- assuming that transactions are not created until syncing is complete
        ptxBlkInfo = const Nothing

        rollbackBlock :: [(CId Addr, HeaderHash)] -> Blund -> WalletModifier
        rollbackBlock dbUsed (b, u) =
            trackingRollbackTxs encSK dbUsed curSlot (\bh -> (mDiff bh, blkHeaderTs bh)) $
            zip3 (gbTxs b) (undoTx u) (repeat $ getBlockHeader b)

        applyBlock :: [(CId Addr, HeaderHash)] -> Blund -> m WalletModifier
        applyBlock dbUsed (b, u) = pure $
            trackingApplyTxs encSK dbUsed (\bh -> (mDiff bh, blkHeaderTs bh, ptxBlkInfo bh)) $
            zip3 (gbTxs b) (undoTx u) (repeat $ getBlockHeader b)

        computeAccModifier :: BlockHeader -> m WalletModifier
        computeAccModifier wHeader = do
            dbUsed <- WS.getCustomAddressesDB WS.UsedAddr
            logInfoS $
                sformat ("Wallet "%build%" header: "%build%", current tip header: "%build)
                wAddr wHeader gstateH
            if | diff gstateH > diff wHeader -> do
                     -- If wallet's syncTip is before than the current tip in the blockchain,
                     -- then it loads wallets starting with @wHeader@.
                     -- Sync tip can be before the current tip
                     -- when we call @syncWalletSetWithTip@ at the first time
                     -- or if the application was interrupted during rollback.
                     -- We don't load blocks explicitly, because blockain can be long.
                     maybe (pure mempty)
                         (\wNextH ->
                            foldlUpWhileM getBlund (applyBlock dbUsed) wNextH loadCond mappendR mempty)
                         =<< resolveForwardLink wHeader
               | diff gstateH < diff wHeader -> do
                     -- This rollback can occur
                     -- if the application was interrupted during blocks application.
                     blunds <- getNewestFirst <$>
                         GS.loadBlundsWhile (\b -> getBlockHeader b /= gstateH) (headerHash wHeader)
                     pure $ foldl' (\r b -> r <> rollbackBlock dbUsed b) mempty blunds
               | otherwise -> mempty <$ logInfoS (sformat ("Wallet "%build%" is already synced") wAddr)

    whenNothing_ wTipHeader $ do
        let wdc = eskToWalletDecrCredentials encSK
            ownGenesisData =
                selectOwnAddresses wdc (txOutAddress . toaOut . snd) $
                M.toList $ unGenesisUtxo genesisUtxo
            ownGenesisUtxo = M.fromList $ map fst ownGenesisData
            ownGenesisAddrs = map snd ownGenesisData
        mapM_ WS.addWAddress ownGenesisAddrs
        WS.updateWalletBalancesAndUtxo (utxoToModifier ownGenesisUtxo)

    startFromH <- maybe firstGenesisHeader pure wTipHeader
    mapModifier@WalletModifier{..} <- computeAccModifier startFromH
    WS.applyModifierToWallet wAddr gstateHHash mapModifier
    -- Mark the wallet as ready, so it will be available from api endpoints.
    WS.setWalletReady wAddr True
    logInfoS $
        sformat ("Wallet "%build%" has been synced with tip "
                %shortHashF%", "%build)
                wAddr (maybe genesisHash headerHash wTipHeader) mapModifier
  where
    firstGenesisHeader :: m BlockHeader
    firstGenesisHeader = resolveForwardLink (genesisHash @BlockHeaderStub) >>=
        maybe (error "Unexpected state: genesisHash doesn't have forward link")
            (maybe (error "No genesis block corresponding to header hash") pure <=< DB.getHeader)

constructAllUsed
    :: [(CId Addr, HeaderHash)]
    -> VoidModifier (CId Addr, HeaderHash)
    -> HashSet (CId Addr)
constructAllUsed dbUsed modif =
    HS.map fst $
    getKeys $
    MM.modifyHashMap modif $
    HM.fromList $
    zip dbUsed (repeat ()) -- not so good performance :(

type TxInfoFunctor = BlockHeader -> (Maybe ChainDifficulty, Maybe Timestamp, Maybe PtxBlockInfo)

trackingApplyTxToModifierM
    :: ( AccountMode m
       , DB.MonadDBRead m
       )
    => CId Wal                  -- ^ Wallet's secret key
    -> [(CId Addr, HeaderHash)] -- ^ All used addresses from db along with their HeaderHashes
    -> WalletModifier           -- ^ Current wallet modifier
    -> (TxAux, TxUndo)          -- ^ Tx with undo
    -> m WalletModifier
trackingApplyTxToModifierM wId dbUsed walMod (txAux, txUndo) = do
    wdc <- eskToWalletDecrCredentials <$> getSKById wId
    tipH <- DB.getTipHeader
    let fInfo = const (Nothing, Nothing, Nothing)
    pure $ trackingApplyTxToModifier wdc dbUsed fInfo walMod (txAux, txUndo, tipH)

-- Process transactions on block application,
-- decrypt our addresses, and add/delete them to/from wallet-db.
-- Addresses are used in TxIn's will be deleted,
-- in TxOut's will be added.
trackingApplyTxs
    :: HasConfiguration
    => EncryptedSecretKey             -- ^ Wallet's secret key
    -> [(CId Addr, HeaderHash)]       -- ^ All used addresses from db along with their HeaderHashes
    -> TxInfoFunctor                  -- ^ Functions to determine tx chain difficulty, timestamp and header hash
    -> [(TxAux, TxUndo, BlockHeader)] -- ^ Txs of blocks and corresponding header hash
    -> WalletModifier
trackingApplyTxs (eskToWalletDecrCredentials -> wdc) dbUsed fInfo txs =
    foldl' (trackingApplyTxToModifier wdc dbUsed fInfo) mempty txs

trackingApplyTxToModifier
    :: HasConfiguration
    => WalletDecrCredentials        -- ^ Wallet's decrypted credentials
    -> [(CId Addr, HeaderHash)]     -- ^ All used addresses from db along with their HeaderHashes
    -> TxInfoFunctor                -- ^ Functions to determine tx chain difficulty, timestamp and header hash
    -> WalletModifier               -- ^ Current CWalletModifier
    -> (TxAux, TxUndo, BlockHeader) -- ^ Tx with undo and corresponding block header
    -> WalletModifier
trackingApplyTxToModifier wdc dbUsed fInfo WalletModifier{..} (tx, undo, blkHeader) = do
    let hh = headerHash blkHeader
        hhs = repeat hh
        wh@(WithHash _ txId) = withHash (taTx tx)
        (mDiff, mTs, mPtxBlkInfo) = fInfo blkHeader
    let thee@THEntryExtra{..} =
            buildTHEntryExtra wdc (wh, undo) (mDiff, mTs)

        ownTxIns = map (fst . fst) theeInputs
        ownTxOuts = map fst theeOutputs

        toPair th = (_thTxId th, th)
        historyModifier =
            maybe wmHistoryEntries
                (\(toPair -> (id, th)) -> MM.insert id th wmHistoryEntries)
                (isTxEntryInteresting thee)

        usedAddrs = map (cwamId . snd) theeOutputs
        changeAddrs = evalChange
                            (constructAllUsed dbUsed wmUsed)
                            (map snd theeInputs)
                            (map snd theeOutputs)
                            (length theeOutputs == NE.length (_txOutputs $ taTx tx))

        newPtxCandidates =
            if | Just ptxBlkInfo <- mPtxBlkInfo
                    -> emmInsert txId ptxBlkInfo wmPtxCandidates
                | otherwise
                    -> wmPtxCandidates
    WalletModifier
        (deleteAndInsertIMM [] (map snd theeOutputs) wmAddresses)
        historyModifier
        (deleteAndInsertVM [] (zip usedAddrs hhs) wmUsed)
        (deleteAndInsertVM [] (zip changeAddrs hhs) wmChange)
        (deleteAndInsertMM ownTxIns ownTxOuts wmUtxo)
        newPtxCandidates

-- Process transactions on block rollback.
-- Like @trackingApplyTxs@, but vise versa.
trackingRollbackTxs
    :: HasConfiguration
    => EncryptedSecretKey -- ^ Wallet's secret key
    -> [(CId Addr, HeaderHash)]                -- ^ All used addresses from db along with their HeaderHashes
    -> SlotId
    -> (BlockHeader
      -> (Maybe ChainDifficulty, Maybe Timestamp))  -- ^ Function to determine tx chain difficulty and timestamp
    -> [(TxAux, TxUndo, BlockHeader)] -- ^ Txs of blocks and corresponding header hash
    -> WalletModifier
trackingRollbackTxs (eskToWalletDecrCredentials -> wdc) dbUsed curSlot fInfo txs =
    foldl' rollbackTx mempty txs
  where
    rollbackTx :: WalletModifier -> (TxAux, TxUndo, BlockHeader) -> WalletModifier
    rollbackTx WalletModifier{..} (tx, undo, blkHeader) = do
        let wh@(WithHash _ txId) = withHash (taTx tx)
            hh = headerHash blkHeader
            hhs = repeat hh
            thee@THEntryExtra{..} =
                buildTHEntryExtra wdc (wh, undo) (fInfo blkHeader)

            ownTxOutIns = map (fst . fst) theeOutputs
            historyModifier =
                maybe wmHistoryEntries
                      (\th -> MM.delete (_thTxId th) wmHistoryEntries)
                      (isTxEntryInteresting thee)
            newPtxCandidates = emmDelete txId (theeTxEntry, curSlot) wmPtxCandidates

        -- Rollback isn't needed, because we don't use @utxoGet@
        -- (undo contains all required information)
        let usedAddrs = map (cwamId . snd) theeOutputs
        let changeAddrs =
                evalChange
                    (constructAllUsed dbUsed wmUsed)
                    (map snd theeInputs)
                    (map snd theeOutputs)
                    (length theeOutputs == NE.length (_txOutputs $ taTx tx))
        WalletModifier
            (deleteAndInsertIMM (map snd theeOutputs) [] wmAddresses)
            historyModifier
            (deleteAndInsertVM (zip usedAddrs hhs) [] wmUsed)
            (deleteAndInsertVM (zip changeAddrs hhs) [] wmChange)
            (deleteAndInsertMM ownTxOutIns (map fst theeInputs) wmUtxo)
            newPtxCandidates

-- Change address is an address which money remainder is sent to.
-- We will consider output address as "change" if:
-- 1. it belongs to source account (taken from one of source addresses)
-- 2. it's not mentioned in the blockchain (aka isn't "used" address)
-- 3. there is at least one non "change" address among all outputs ones

-- The first point is very intuitive and needed for case when we
-- send tx to somebody, i.e. to not our address.
-- The second point is needed for case when
-- we send a tx from our account to the same account.
-- The third point is needed for case when we just created address
-- in an account and then send a tx from the address belonging to this account
-- to the created.
-- In this case both output addresses will be treated as "change"
-- by the first two rules.
-- But the third rule will make them not "change".
-- This decision is controversial, but we can't understand from the blockchain
-- which of them is really "change".
-- There is an option to treat both of them as "change", but it seems to be more puzzling.
evalChange
    :: HashSet (CId Addr)
    -> [CWAddressMeta] -- ^ Own input addresses of tx
    -> [CWAddressMeta] -- ^ Own outputs addresses of tx
    -> Bool            -- ^ Whether all tx's outputs are our own
    -> [CId Addr]
evalChange allUsed inputs outputs allOutputsOur
    | [] <- inputs = [] -- It means this transaction isn't our outgoing transaction.
    | inp : _ <- inputs =
        let srcAccount = addrMetaToAccount inp in
        -- Apply the first point.
        let addrFromSrcAccount = HS.fromList $ map cwamId $ filter ((== srcAccount) . addrMetaToAccount) outputs in
        -- Apply the second point.
        let potentialChange = addrFromSrcAccount `HS.difference` allUsed in
        -- Apply the third point.
        if allOutputsOur && potentialChange == HS.fromList (map cwamId outputs) then []
        else HS.toList potentialChange

setLogger :: HasLoggerName m => m a -> m a
setLogger = modifyLoggerName (<> "wallet" <> "sync")
