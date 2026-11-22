-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_L1_pos
-- name    : Kyprianou.Ch08.StageB.p2m81_drawdown_L1_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T01:55:35.21804+00:00
-- url     : https://prove2.me/theorems/4d82e66c-0b43-4077-a64c-b993203092c1
-- title:
--   Rate-one Laplace value strictly positive
-- statement:
--   The rate-one Laplace integrand is everywhere strictly positive, so its support is univ and the integral over a probability measure is strictly positive. Leaf fact feeding the real Laplace bounds.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_drawdown_L1_pos
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 < (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂μ) := by
  sorry
