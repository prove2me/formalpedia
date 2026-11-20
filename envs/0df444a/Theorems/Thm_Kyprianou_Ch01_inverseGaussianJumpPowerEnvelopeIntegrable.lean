-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianJumpPowerEnvelopeIntegrable
-- name    : Kyprianou.Ch01.inverseGaussianJumpPowerEnvelopeIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:09:54.650972+00:00
-- url     : https://prove2.me/theorems/ae0331e3-d1b0-451f-98ed-28db5b1677b9
-- title:
--   Integrable half-power / three-halves envelope for inverse Gaussian Fourier jump kernel
-- statement:
--   For any Fourier frequency theta, (|theta|+2) times the x^(-1/2) near-origin and x^(-3/2) far-tail envelope is Lebesgue integrable over x>0. The index-1/2 Gamma power-envelope theorem already in the formal library proves this by scaling.
-- source:
--   Kyprianou (2006) Chapter 1 inverse-Gaussian Lévy exponent, exact density-weighted kernel analytic lemma.

import Mathlib
open MeasureTheory Set Complex ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianJumpPowerEnvelopeIntegrable
    (theta : ℝ) :
    IntegrableOn (fun x : ℝ =>
      (|theta| + 2) *
        (if x ≤ 1 then x ^ (-(1 / 2 : ℝ))
          else x ^ (-(3 / 2 : ℝ)))) (Set.Ioi (0 : ℝ)) volume := by
  sorry
