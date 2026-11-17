-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gaussianMarginalCharFunVariance
-- name    : Kyprianou.Ch01.gaussianMarginalCharFunVariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T20:32:27.526723+00:00
-- url     : https://prove2.me/theorems/287646c3-18fc-47cf-a51d-a9a7f5f2ce5b
-- title:
--   Zero-mean Gaussian characteristic function in explicit real variance form
-- statement:
--   For any nonnegative Gaussian variance v and real Fourier frequency xi, the characteristic function of the zero-mean real Gaussian probability measure is exactly exp(-v xi squared / two), using the real-to-complex coercions required by Kyprianou Chapter 1 Theorem 1.6. This is a source-conservative direct corollary of the pinned Mathlib theorem ProbabilityTheory.charFun_gaussianReal, and helps compose a Gaussian Brownian component with a proved independent pure-jump Lévy process.
-- source:
--   Kyprianou (2006), Chapter 1, Lévy–Khintchine Gaussian term and Theorem 1.6; pinned Mathlib ProbabilityTheory.charFun_gaussianReal in Mathlib.Probability.Distributions.Gaussian.Real.

import Mathlib.Probability.Distributions.Gaussian.Real
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.gaussianMarginalCharFunVariance
    (v : ℝ≥0) (ξ : ℝ) :
    charFun (gaussianReal 0 v) ξ =
      Complex.exp (-(((v : ℝ) : ℂ) * (ξ : ℂ) ^ 2 / 2)) := by
  sorry
