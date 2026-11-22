-- Prove2me | Theorems.Thm_MatchingLogic_freshWitnessed_of_witnessed_of_supply
-- name    : MatchingLogic.freshWitnessed_of_witnessed_of_supply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:32:43.00517+00:00
-- url     : https://prove2.me/theorems/92fcdb5b-b61d-4272-9a8c-43fc118fbd72
-- title:
--   Matching Logic: fresh Witnessed of witnessed of supply
-- statement:
--   An infinite supply of usable witnesses upgrades ordinary witnessedness to
--   raw-fresh witnessedness.  The proof is short: `p.allVars` is finite.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessSupply.lean#L49-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessSupply.lean#L49-L55

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessSupply
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}

theorem MatchingLogic.freshWitnessed_of_witnessed_of_supply
    {Gamma : Set (Pattern S Nat)} (hSupply : InfiniteWitnessSupply Gamma) :
    FreshWitnessed Gamma := by sorry
