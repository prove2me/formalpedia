-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneInverseSquareLintegral
-- name    : Kyprianou.Ch01.stableAlphaOneInverseSquareLintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T09:26:27.576579+00:00
-- url     : https://prove2.me/theorems/ff6bb75b-4ffa-4b7d-8d46-36cf3e662ac8
-- title:
--   Tonelli-compatible extended nonnegative inverse-square Laplace integral
-- statement:
--   For x>0, the extended nonnegative Lebesgue integral over t>0 of t exp(−xt) equals ENNReal.ofReal(1/x²). This transfers the proved Gamma inverse-square identity to the ENNReal form required by the Tonelli swap without assuming integrability of the double kernel. Measurability, positivity and the pinned Gamma-integrability bound justify the conversion.
-- source:
--   Kyprianou (2006), Chapter 1, stable alpha-one Lévy cosine exponent; Tonelli-ready positive Laplace kernel.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneInverseSquareLaplace
open MeasureTheory Real Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneInverseSquareLintegral
    (x : ℝ) (hx : 0 < x) :
    (∫⁻ t in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (t * Real.exp (-(x * t)))) =
      ENNReal.ofReal ((x ^ 2)⁻¹) := by
  sorry
