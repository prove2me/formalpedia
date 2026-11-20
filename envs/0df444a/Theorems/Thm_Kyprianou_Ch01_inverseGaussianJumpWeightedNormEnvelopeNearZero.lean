-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianJumpWeightedNormEnvelopeNearZero
-- name    : Kyprianou.Ch01.inverseGaussianJumpWeightedNormEnvelopeNearZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:12:47.91024+00:00
-- url     : https://prove2.me/theorems/bb4498c3-ec61-4ba8-937a-e171b89f6175
-- title:
--   Inverse Gaussian Fourier jump weighted norm NearZero local estimate
-- statement:
--   For every b>0 and 0<x≤1 the true inverse Gaussian density weighted original complex jump Fourier remainder is bounded by (|theta|+2)x^(-1/2). The density is O(x^-3/2), and |1−exp(iθx)|≤|θ|x.
-- source:
--   Kyprianou (2006) Chapter 1 inverse-Gaussian Lévy exponent, exact density-weighted kernel analytic lemma.

import Mathlib
open MeasureTheory Set Complex ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianJumpWeightedNormEnvelopeNearZero
    (b theta x : ℝ) (hb : 0 < b) (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖(ENNReal.ofReal
         ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
           Real.exp (-(b ^ 2 * x / 2)))).toReal •
           ((1 : ℂ) - Complex.exp
             (Complex.I * ((theta * x : ℝ) : ℂ)))‖ ≤ (|theta| + 2) * x ^ (-(1 / 2 : ℝ)) := by
  sorry
