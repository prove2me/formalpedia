-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaKernelIntegral
-- name    : Kyprianou.Ch01.stableGammaKernelIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T20:59:02.819268+00:00
-- url     : https://prove2.me/theorems/0981ae7c-cfe6-47ac-a5a0-c0115f7d069f
-- title:
--   Gamma Laplace kernel for positive stable index below one
-- statement:
--   The scaled Gamma Laplace integral ∫_0∞ e^(-ux) x^(-alpha) dx for alpha in (0,1) equals u^(alpha-1) Γ(1-alpha). Derive directly by reusing the pinned Mathlib theorem Real.integral_rpow_mul_exp_neg_mul_Ioi with its a=1-alpha and r=u parameters. This is the explicit remaining kernel after integrating by parts in the stable Lévy exponent exercise.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4(i), solution p.301 / PDF p.155, equation S.2.

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaKernelIntegral
    (alpha u : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hu : 0 < u) :
    (∫ x in Set.Ioi (0 : ℝ),
      Real.exp (-(u * x)) * x ^ (-alpha) ∂volume) =
      (1 / u) ^ (1 - alpha) * Real.Gamma (1 - alpha) := by sorry
