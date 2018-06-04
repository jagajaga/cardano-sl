-- | READ-only operations on the wallet-spec state
module Cardano.Wallet.Kernel.DB.Spec.Read (
    -- * Reads
    accountTotalBalance
  , accountUtxo
  ) where

import           Universum

import qualified Pos.Core as Core
import           Pos.Crypto (EncryptedSecretKey)
import           Pos.Txp (Utxo)

import           Cardano.Wallet.Kernel.PrefilterTx (utxoForAccount)

import           Cardano.Wallet.Kernel.DB.HdWallet
import           Cardano.Wallet.Kernel.DB.InDb
import           Cardano.Wallet.Kernel.DB.Spec
import           Cardano.Wallet.Kernel.DB.Spec.Util

{-------------------------------------------------------------------------------
  Pure functions that support read-only operations on an account Checkpoint, as
  defined in the Wallet Spec
-------------------------------------------------------------------------------}

accountUtxo :: Checkpoint -> Utxo
accountUtxo = view (checkpointUtxo . fromDb)

accountUtxoBalance :: Checkpoint -> Core.Coin
accountUtxoBalance = view (checkpointUtxoBalance . fromDb)

accountPendingTxs :: Checkpoint -> PendingTxs
accountPendingTxs = view (checkpointPending . pendingTransactions . fromDb)

-- | The Available Balance is the cached utxo balance minus any (pending) spent utxo
accountAvailableBalance :: Checkpoint -> Core.Coin
accountAvailableBalance c =
    fromMaybe subCoinErr balance'
    where
        subCoinErr = error "Coin arithmetic error: subCoin utxoBalance balanceDelta"

        pendingIns = txIns (accountPendingTxs c)
        spentUtxo  = utxoRestrictToInputs (accountUtxo c) pendingIns

        balance' = Core.subCoin (accountUtxoBalance c) (balance spentUtxo)

-- | Account Change refers to any pending outputs paid back into the
--   account (represented by the given checkpoint).
--
-- NOTE: computing 'change' requires prefiltering
accountChange :: (Utxo -> Utxo) -> Checkpoint -> Utxo
accountChange ourUtxo
    = ourUtxo . pendingUtxo . accountPendingTxs

-- | The Account Total Balance is the 'available' balance plus any 'change'
--
-- NOTE: computing 'total balance' requires prefiltering, which requires
--       the wallet ESK and HdAccountId.
accountTotalBalance :: EncryptedSecretKey -> HdAccountId -> Checkpoint -> Core.Coin
accountTotalBalance esk accountId c
    = add' availableBalance changeBalance
    where
        add' = Core.unsafeAddCoin
        ourUtxo' = utxoForAccount accountId esk

        availableBalance = accountAvailableBalance c
        changeBalance    = balance (accountChange ourUtxo' c)
