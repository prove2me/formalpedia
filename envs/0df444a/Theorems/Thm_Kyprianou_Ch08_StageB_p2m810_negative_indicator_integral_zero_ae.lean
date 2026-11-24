-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_negative_indicator_integral_zero_ae
-- name    : Kyprianou.Ch08.StageB.p2m810_negative_indicator_integral_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:36:55.25874+00:00
-- url     : https://prove2.me/theorems/e644015d-d7c6-4b65-aacd-56d5011e5e6c
-- title:
--   Zero negative-threshold indicator integral implies almost sure lower bound
-- statement:
--   A measurable bounded indicator of the event Y<c has zero integral; hence it vanishes almost surely and Y is at least c.
-- source:
--   MeasureTheory integral_eq_zero_iff_of_nonneg; Theorem 8.10(i).

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
/-- Zero indicator expectation forces the event to be null. -/
theorem p2m810_negative_indicator_integral_zero_ae :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (Y : Ω → ℝ) (c : ℝ),
      AEMeasurable Y P →
      (∫ ω, if Y ω<c then (1:ℝ) else 0 ∂P) = 0 →
      ∀ᵐ ω ∂P, c ≤ Y ω := by
  sorry
end Kyprianou.Ch08.StageB
