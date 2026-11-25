-- Prove2me | Theorems.Thm_GlobalTheory_HL_split_by_target
-- name    : GlobalTheory.HL.split_by_target
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:52:32.788925+00:00
-- url     : https://prove2.me/theorems/1de98436-9324-458f-a1fb-49cfb6d9e244
-- title:
--   HL: split by target
-- statement:
--   The HL construction uses the split by target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermDoubleCosetMovesFiniteTargetsSplit.lean#L15-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermDoubleCosetMovesFiniteTargetsSplit.lean#L15-L148

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetMoveTermWeightCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralLinearPositiveNormBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFineSubgroupMovesAtLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermDoubleCosetMovesFiniteTargetsSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL

theorem GlobalTheory.HL.split_by_target {W Y Z : Type} [AddCommGroup W] (A B : AddSubgroup W) (M : W → Prop) (m : W → Z)
    (f : Y → Z) (hf : Function.Injective f) (hB : Fine A (ind M) B)
    (hm : ∀ w, M w → ∀ b ∈ B, m (w + b) = m w) (hex : ∀ w, M w → ∃ y, f y = m w) (c : ℝ) (hc : 0 ≤ c) :
    {y | ∃ w, M w ∧ f y = m w}.Finite ∧ (∀ y, Nice A (ind fun w => M w ∧ f y = m w)) ∧
    {y | c * (cint A (ind fun w => M w ∧ f y = m w)).re ≠ 0}.Finite ∧
    (∀ y, 0 ≤ c * (cint A (ind fun w => M w ∧ f y = m w)).re) ∧
    ∀ (P : Y → Prop) (g : Y → ℂ) (G : W → ℂ), (∀ w y, (M w ∧ f y = m w) → G w = if P y then g y else 0) →
      (∀ w, ¬ M w → G w = 0) → Nice A G ∧
      ∑ᶠ y : {y // P y}, ((c * (cint A (ind fun w => M w ∧ f y = m w)).re : ℝ) : ℂ) * g y =
        (c : ℂ) * cint A G := by sorry
