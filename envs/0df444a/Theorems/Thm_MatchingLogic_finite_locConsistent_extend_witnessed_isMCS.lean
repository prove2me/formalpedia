-- Prove2me | Theorems.Thm_MatchingLogic_finite_locConsistent_extend_witnessed_isMCS
-- name    : MatchingLogic.finite_locConsistent_extend_witnessed_isMCS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:06.38532+00:00
-- url     : https://prove2.me/theorems/d5353f2c-cb1a-41b2-a2b7-19ff9c2950c6
-- title:
--   Matching Logic: finite loc Consistent extend witnessed is MCS
-- statement:
--   Every locally consistent finite-list theory over a countable pattern
--   language extends to a witnessed maximal locally consistent set.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean#L391-L399
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean#L391-L399

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Mathlib.Data.Countable.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatWitnessed

theorem MatchingLogic.finite_locConsistent_extend_witnessed_isMCS
    [Countable (Pattern S Nat)] (base : List (Pattern S Nat))
    (hbase : LocConsistent ({q | q ∈ base} : Set (Pattern S Nat))) :
    ∃ Delta : Set (Pattern S Nat),
      ({q | q ∈ base} : Set (Pattern S Nat)) ⊆ Delta ∧
      IsMCS Delta ∧ Witnessed Delta := by sorry
