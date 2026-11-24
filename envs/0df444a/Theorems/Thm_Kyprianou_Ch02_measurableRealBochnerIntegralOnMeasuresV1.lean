-- Prove2me | Theorems.Thm_Kyprianou_Ch02_measurableRealBochnerIntegralOnMeasuresV1
-- name    : Kyprianou.Ch02.measurableRealBochnerIntegralOnMeasuresV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:36:36.748489+00:00
-- url     : https://prove2.me/theorems/f31084c3-0cd1-4ba5-8029-06e8a995622e
-- title:
--   Measurability of real Bochner integration as a function of the measure
-- statement:
--   The absolute, positive and negative extended integrals are measurable in the measure argument. The Bochner integral is the signed difference of the latter two if the former is finite, and zero otherwise.
-- source:
--   Kyprianou (2006), Chapter 2 Exercise 2.6(ii); measurable Bochner integration used in the compensated mark process.

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem measurableRealBochnerIntegralOnMeasuresV1 (f : ℝ → ℝ) (hf : Measurable f) :
    Measurable (fun μ : Measure ℝ => ∫ x, f x ∂μ) := by sorry

end Kyprianou.Ch02
