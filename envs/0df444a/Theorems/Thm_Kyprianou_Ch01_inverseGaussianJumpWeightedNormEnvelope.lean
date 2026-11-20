-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianJumpWeightedNormEnvelope
-- name    : Kyprianou.Ch01.inverseGaussianJumpWeightedNormEnvelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:09:57.08063+00:00
-- url     : https://prove2.me/theorems/d8d9fd34-54f1-492c-9b2e-a7e98bb88fa4
-- title:
--   Pointwise inverse Gaussian Fourier jump kernel density dominated by integrable power envelope
-- statement:
--   For x>0, the exact original inverse Gaussian density times the norm of the original Fourier jump kernel 1-exp(iθx) is at most (|θ|+2)x^(-1/2) for x≤1 and (|θ|+2)x^(-3/2) for x>1. Uses the real imaginary exponential Lipschitz estimate near zero and the global bound 2 at infinity, with exponential tilt and sqrt(2π) normalisation.
-- source:
--   Kyprianou (2006) Chapter 1 inverse-Gaussian Lévy exponent, exact density-weighted kernel analytic lemma.

import Mathlib
open MeasureTheory Set Complex ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianJumpWeightedNormEnvelope
    (b theta x : ℝ) (hb : 0 < b) (hx : 0 < x) :
    ‖(ENNReal.ofReal
         ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
           Real.exp (-(b ^ 2 * x / 2)))).toReal •
           ((1 : ℂ) - Complex.exp
             (Complex.I * ((theta * x : ℝ) : ℂ)))‖ ≤ (|theta| + 2) * (if x ≤ 1 then x ^ (-(1 / 2 : ℝ)) else x ^ (-(3 / 2 : ℝ))) := by
  sorry
