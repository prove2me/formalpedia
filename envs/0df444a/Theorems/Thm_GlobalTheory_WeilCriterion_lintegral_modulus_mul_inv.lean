-- Prove2me | Theorems.Thm_GlobalTheory_WeilCriterion_lintegral_modulus_mul_inv
-- name    : GlobalTheory.WeilCriterion.lintegral_modulus_mul_inv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:52:37.428192+00:00
-- url     : https://prove2.me/theorems/4094e711-7f47-45bd-ae46-a872a00fde7b
-- title:
--   Weil Criterion: lintegral modulus mul inv
-- statement:
--   The Weil Criterion construction uses the lintegral modulus mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeilCriterionInvariantMeasureHomogeneousSpace.lean#L45-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeilCriterionInvariantMeasureHomogeneousSpace.lean#L45-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBruhatFunctionClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeilCriterionInvariantMeasureHomogeneousSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.WeilCriterion
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem GlobalTheory.WeilCriterion.lintegral_modulus_mul_inv (μ : Measure G) [μ.IsHaarMeasure] {f : G → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, (modularCharacterFun x : ℝ≥0∞) * f x⁻¹ ∂μ = ∫⁻ x, f x ∂μ := by sorry
