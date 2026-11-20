-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianJumpWeightedNormEnvelopeTail
-- name    : Kyprianou.Ch01.inverseGaussianJumpWeightedNormEnvelopeTail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:12:46.265019+00:00
-- url     : https://prove2.me/theorems/a001966d-b61e-46dc-84bf-72f748e7800c
-- title:
--   Inverse Gaussian Fourier jump weighted norm Tail local estimate
-- statement:
--   For every b>0 and x>1 the true inverse Gaussian density weighted original complex jump Fourier remainder is bounded by (|theta|+2)x^(-3/2). The exponentially tilted density is bounded by x^-3/2 and the Fourier difference has norm at most 2.
-- source:
--   Kyprianou (2006) Chapter 1 inverse-Gaussian Lévy exponent, exact density-weighted kernel analytic lemma.

import Mathlib
open MeasureTheory Set Complex ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianJumpWeightedNormEnvelopeTail
    (b theta x : ℝ) (hb : 0 < b) (hx : 1 < x) :
    ‖(ENNReal.ofReal
         ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
           Real.exp (-(b ^ 2 * x / 2)))).toReal •
           ((1 : ℂ) - Complex.exp
             (Complex.I * ((theta * x : ℝ) : ℂ)))‖ ≤ (|theta| + 2) * x ^ (-(3 / 2 : ℝ)) := by
  sorry
