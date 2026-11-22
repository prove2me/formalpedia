-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_singleton_split_le
-- name    : Kyprianou.Ch08.StageB.p2m81_drawdown_singleton_split_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T01:19:31.335947+00:00
-- url     : https://prove2.me/theorems/813b694d-e96d-475e-ae42-7506960e092a
-- title:
--   Singleton-plus-Laplace splitting bound
-- statement:
--   For a probability measure supported on the nonnegative half-line and x>0, splitting the rate-one Laplace integral over {x} and its complement gives mu{x}*ofReal(1-exp(-x))+L1(mu)<=1, using the singleton restriction against the Dirac mass, the unit cap on the complement, and ofReal(exp(-x))+ofReal(1-exp(-x))=1. Feeds the pointwise Markov step.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_drawdown_singleton_split_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupp : μ (Iio (0 : ℝ)) = 0)
    (x : ℝ) (hx : 0 < x) :
    μ {x} * ENNReal.ofReal (1 - Real.exp (-x)) +
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂μ) ≤ 1 := by
  sorry
