-- Prove2me | Theorems.Thm_GlobalTheory_IntegralAgainstMeasure_integralAgainstLinear_apply
-- name    : GlobalTheory.IntegralAgainstMeasure.integralAgainstLinear_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:58.178821+00:00
-- url     : https://prove2.me/theorems/42351615-c9b1-4b9d-8377-5c9318ba4c2c
-- title:
--   Integral Against Measure: integral Against Linear apply
-- statement:
--   The Integral Against Measure construction uses the integral Against Linear apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IntegralAgainstLinearApply.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IntegralAgainstLinearApply.lean#L25-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IntegralAgainstLinearApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.IntegralAgainstMeasure
variable {K B : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
  [OpensMeasurableSpace K] [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem GlobalTheory.IntegralAgainstMeasure.integralAgainstLinear_apply (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B))
    (f : C(K, ℂ)) : integralAgainstLinear μ p f = ∫ k, f k • p k ∂μ := by sorry

attribute [defeq] GlobalTheory.IntegralAgainstMeasure.integralAgainstLinear_apply
