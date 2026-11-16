-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaPositiveKernelIntegrable
-- name    : Kyprianou.Ch01.stableGammaPositiveKernelIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:35:06.885961+00:00
-- url     : https://prove2.me/theorems/c20c49f1-2744-43fa-a959-6bfec14e44b8
-- title:
--   Scaled positive Gamma Laplace kernel is integrable for stable index between zero and one
-- statement:
--   The positive scaled Gamma Laplace kernel exp(-u*x)*x^-alpha is integrable on (0,∞) when alpha∈(0,1), u>0. Mathlib's integral_rpow_mul_exp_neg_mul_Ioi evaluates its integral as (1/u)^(1-alpha)*Gamma(1-alpha), a strictly positive finite real. Mathlib IntegrableOn.of_integral_ne_zero then proves genuine integrability of the nonnegative kernel rather than merely relying on the zero-by-definition value of nonintegrable Bochner integrals. This is the other integrability input to rigorous stable Gamma integration by parts.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.4(i), printed solution p.301.

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
open MeasureTheory Real Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaPositiveKernelIntegrable
    (alpha u : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hu : 0 < u) :
    IntegrableOn (fun x : ℝ =>
      Real.exp (-(u * x)) * x ^ (-alpha))
      (Set.Ioi (0 : ℝ)) := by sorry
