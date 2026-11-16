-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueExpDeficit_div_tendsto_mean
-- name    : Kyprianou.Ch01.queueExpDeficit_div_tendsto_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T12:11:10.601725+00:00
-- url     : https://prove2.me/theorems/2f591a66-2508-4ebb-b3d7-2166541fef4c
-- title:
--   Exponential-deficit integral difference quotient converges to the mean from the right
-- statement:
--   As θ decreases to zero through positive values, the expectation of (1−exp(−θX))/θ converges to E[X] for a positive random variable of finite expectation. The pointwise limit is X, and the quotient is dominated by X, permitting dominated convergence.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.9(i), derivative of M/G/1 queue adjustment exponent at the origin

import Mathlib
open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.queueExpDeficit_div_tendsto_mean
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (hfiniteMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hmean : (∫ x, x ∂F) = mu) :
    Tendsto (fun theta : ℝ =>
      (∫ x : ℝ, (1 - Real.exp (-theta * x)) ∂F) / theta)
      (𝓝[>] (0 : ℝ)) (𝓝 mu) := by sorry
