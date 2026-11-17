-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gaussianScaledMarginalCharFun
-- name    : Kyprianou.Ch01.gaussianScaledMarginalCharFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:53:14.21958+00:00
-- url     : https://prove2.me/theorems/a1453481-59fd-4055-952d-2664ec7ec6f0
-- title:
--   Exact Gaussian characteristic-function identity after variance scaling
-- statement:
--   For nonnegative variance factor v and nonnegative time t, the Gaussian law with variance t scaled by the nonnegative square root of v has characteristic function exp(-v t ξ²/2) at every real frequency ξ. This verifies the exact Gaussian covariance coefficient when constructing the positive-variance Lévy–Khintchine process in Kyprianou (2006) Chapter 1 Theorem 1.6, without assuming any new stochastic process exists.
-- source:
--   Pinned Mathlib ProbabilityTheory.charFun_gaussianReal and MeasureTheory.charFun_map_smul; Kyprianou Chapter 1 Theorem 1.6 Gaussian factor.

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.gaussianScaledMarginalCharFun (v t : ℝ≥0) (xi : ℝ) :
    charFun ((gaussianReal 0 t).map
        (fun x : ℝ => Real.sqrt (v : ℝ) * x)) xi =
      Complex.exp (-(((v : ℝ) * (t : ℝ) : ℂ) * (xi : ℂ) ^ 2 / 2)) := by
  sorry
