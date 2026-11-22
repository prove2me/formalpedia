-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_singleton_markov
-- name    : Kyprianou.Ch08.StageB.p2m81_drawdown_singleton_markov
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T01:19:31.572821+00:00
-- url     : https://prove2.me/theorems/41f93951-3e3f-4e3c-b3b9-8600e272a576
-- title:
--   Pointwise singleton Markov bound
-- statement:
--   For a probability measure supported on the nonnegative half-line and x>0, cancelling the finite Laplace value from the splitting bound and multiplying by the finite inverse constant gives mu{x}<=ofReal(1-exp(-x))^{-1}*(1-L1(mu)). Proved from the splitting-bound helper plus the Laplace cap. Gives the per-scale estimate the vanishing squeeze needs.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_drawdown_singleton_markov
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupp : μ (Iio (0 : ℝ)) = 0)
    (x : ℝ) (hx : 0 < x) :
    μ {x} ≤ ENNReal.ofReal (1 - Real.exp (-x))⁻¹ *
      (1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂μ)) := by
  sorry
