-- Prove2me | Theorems.Thm_MatchingLogic_locConsistent_extend_freshWitnessed_isMCS
-- name    : MatchingLogic.locConsistent_extend_freshWitnessed_isMCS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:32:47.163871+00:00
-- url     : https://prove2.me/theorems/301f91cf-d684-4d34-ba1b-098a6965d214
-- title:
--   Matching Logic: loc Consistent extend fresh Witnessed is MCS
-- statement:
--   A locally consistent set extends to a fresh-witnessed MCS provided the
--   starting syntax leaves an infinite reserve of variables free in none of its
--   members.  This is the additional hypothesis that the raw-`Nat` formulation
--   needs in place of the source's extension from `V` to `V⁺`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessSupply.lean#L219-L236
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessSupply.lean#L219-L236

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
noncomputable section
attribute [local instance] MatchingLogic.witnessSupplyDecidableEqPattern

theorem MatchingLogic.locConsistent_extend_freshWitnessed_isMCS
    [Countable (Pattern S Nat)] {Gamma : Set (Pattern S Nat)}
    (hGamma : LocConsistent Gamma)
    (hSupply : InfiniteFreshVariableSupply Gamma) :
    ∃ Delta : Set (Pattern S Nat),
      Gamma ⊆ Delta ∧ IsMCS Delta ∧ FreshWitnessed Delta := by sorry
