-- Prove2me | Theorems.Thm_GlobalTheory_WeilCriterion_lintegral_mul_right_eq_modulus
-- name    : GlobalTheory.WeilCriterion.lintegral_mul_right_eq_modulus
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:53:28.038355+00:00
-- url     : https://prove2.me/theorems/641083a4-8f44-4675-a040-bd1fee9764a4
-- title:
--   Weil Criterion: lintegral mul right eq modulus
-- statement:
--   The Weil Criterion construction uses the lintegral mul right eq modulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeilCriterionInvariantMeasureHomogeneousSpace.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeilCriterionInvariantMeasureHomogeneousSpace.lean#L16-L21

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

theorem GlobalTheory.WeilCriterion.lintegral_mul_right_eq_modulus (μ : Measure G) [μ.IsHaarMeasure] {f : G → ℝ≥0∞}
    (hf : Measurable f) (g : G) :
    ∫⁻ x, f (x * g) ∂μ = (modularCharacterFun g : ℝ≥0∞) * ∫⁻ x, f x ∂μ := by sorry
