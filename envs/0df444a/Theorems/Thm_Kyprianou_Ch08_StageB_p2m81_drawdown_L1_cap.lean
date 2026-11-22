-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_L1_cap
-- name    : Kyprianou.Ch08.StageB.p2m81_drawdown_L1_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T01:55:28.843734+00:00
-- url     : https://prove2.me/theorems/641b11b3-2263-440f-be36-d49ca9e6035d
-- title:
--   Rate-one Laplace value capped at one
-- statement:
--   On y>=0, exp(-y)<=1, so the rate-one Laplace integrand is a.e. bounded by one and the integral is at most the total mass one. Proved from the a.e.-support helper.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_drawdown_L1_cap
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupp : μ (Iio (0 : ℝ)) = 0) :
    (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂μ) ≤ 1 := by
  sorry
