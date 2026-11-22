-- Prove2me | Theorems.Thm_MatchingLogic_finite_locConsistent_extend_witnessed_isMCS_of_surjective
-- name    : MatchingLogic.finite_locConsistent_extend_witnessed_isMCS_of_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:54.725655+00:00
-- url     : https://prove2.me/theorems/df96ce08-3a12-4f9c-b4b3-e59db515b1a2
-- title:
--   Matching Logic: finite loc Consistent extend witnessed is MCS of surjective
-- statement:
--   Enumeration-parametric ordinary witnessedness follows by forgetting the
--   freshness evidence from the stronger construction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean#L363-L373
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean#L363-L373

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

theorem MatchingLogic.finite_locConsistent_extend_witnessed_isMCS_of_surjective
    (enum : Nat → Pattern S Nat) (henum : Function.Surjective enum)
    (base : List (Pattern S Nat))
    (hbase : LocConsistent ({q | q ∈ base} : Set (Pattern S Nat))) :
    ∃ Delta : Set (Pattern S Nat),
      ({q | q ∈ base} : Set (Pattern S Nat)) ⊆ Delta ∧
      IsMCS Delta ∧ Witnessed Delta := by sorry
