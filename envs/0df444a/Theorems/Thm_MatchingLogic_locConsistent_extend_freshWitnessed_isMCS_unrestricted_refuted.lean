-- Prove2me | Theorems.Thm_MatchingLogic_locConsistent_extend_freshWitnessed_isMCS_unrestricted_refuted
-- name    : MatchingLogic.locConsistent_extend_freshWitnessed_isMCS_unrestricted_refuted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:32:49.064398+00:00
-- url     : https://prove2.me/theorems/ceffd6ba-dd66-435a-9cd8-7888640d14a4
-- title:
--   Matching Logic: loc Consistent extend fresh Witnessed is MCS unrestricted refuted
-- statement:
--   The same extension statement without a variable-supply hypothesis is
--   false.  Taking the existing witnessed-but-not-fresh MCS as the starting set
--   leaves no locally consistent proper extension in which freshness could be
--   repaired.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessSupply.lean#L242-L258
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessSupply.lean#L242-L258

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

theorem MatchingLogic.locConsistent_extend_freshWitnessed_isMCS_unrestricted_refuted :
    ¬ (∀ {Gamma : Set (Pattern WitnessCollapseSig Nat)},
      LocConsistent Gamma →
        ∃ Delta : Set (Pattern WitnessCollapseSig Nat),
          Gamma ⊆ Delta ∧ IsMCS Delta ∧ FreshWitnessed Delta) := by sorry
