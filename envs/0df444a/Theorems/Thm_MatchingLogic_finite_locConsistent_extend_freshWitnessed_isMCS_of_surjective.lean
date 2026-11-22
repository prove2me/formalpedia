-- Prove2me | Theorems.Thm_MatchingLogic_finite_locConsistent_extend_freshWitnessed_isMCS_of_surjective
-- name    : MatchingLogic.finite_locConsistent_extend_freshWitnessed_isMCS_of_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:15.077136+00:00
-- url     : https://prove2.me/theorems/e2aaf4e0-c3fa-4026-a5d3-9b9ec5ba6329
-- title:
--   Matching Logic: finite loc Consistent extend fresh Witnessed is MCS of surjective
-- statement:
--   The finite Henkin construction preserves the raw freshness of the
--   adjoined witness name, not merely the ordinary witnessed property.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean#L347-L359
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean#L347-L359

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

theorem MatchingLogic.finite_locConsistent_extend_freshWitnessed_isMCS_of_surjective
    (enum : Nat → Pattern S Nat) (henum : Function.Surjective enum)
    (base : List (Pattern S Nat))
    (hbase : LocConsistent ({q | q ∈ base} : Set (Pattern S Nat))) :
    ∃ Delta : Set (Pattern S Nat),
      ({q | q ∈ base} : Set (Pattern S Nat)) ⊆ Delta ∧
      IsMCS Delta ∧ FreshWitnessed Delta := by sorry
