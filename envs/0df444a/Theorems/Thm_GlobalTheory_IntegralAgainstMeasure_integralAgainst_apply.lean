-- Prove2me | Theorems.Thm_GlobalTheory_IntegralAgainstMeasure_integralAgainst_apply
-- name    : GlobalTheory.IntegralAgainstMeasure.integralAgainst_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:59.825254+00:00
-- url     : https://prove2.me/theorems/4711428f-2aec-4a9c-a620-0ce024e319c3
-- title:
--   Integral Against Measure: integral Against apply
-- statement:
--   The Integral Against Measure construction uses the integral Against apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IntegralAgainstLinearApply.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IntegralAgainstLinearApply.lean#L40-L41

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

theorem GlobalTheory.IntegralAgainstMeasure.integralAgainst_apply (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B))
    (f : C(K, ℂ)) : integralAgainst μ p f = ∫ k, f k • p k ∂μ := by sorry

attribute [defeq] GlobalTheory.IntegralAgainstMeasure.integralAgainst_apply
