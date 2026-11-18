-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneWeightedInverseSquareLintegral
-- name    : Kyprianou.Ch01.stableAlphaOneWeightedInverseSquareLintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T09:29:43.154779+00:00
-- url     : https://prove2.me/theorems/34746b91-b50d-4fa4-b683-6debb4223a6f
-- title:
--   Weighted Tonelli-side inverse-square Laplace integral with nonnegative cosine deficit
-- statement:
--   For x>0, integrating the extended nonnegative Laplace kernel a exp(−a x)(1−cos x) over positive a yields ENNReal.ofReal((1−cos x)/x²). The numerator is nonnegative and independent of a, so it factors out of the Tonelli integral. The remaining integral equals 1/x² by the previously proved Gamma-based ENNReal Laplace identity. This is the left inner integral needed to complete the π/2 cosine evaluation.
-- source:
--   Kyprianou (2006), Chapter 1, α=1 stable Lévy cosine exponent; Tonelli Gamma kernel.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneInverseSquareLintegral
open MeasureTheory Real Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneWeightedInverseSquareLintegral
    (x : ℝ) (hx : 0 < x) :
    (∫⁻ a in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (a * Real.exp (-(a * x)) * (1 - Real.cos x))) =
      ENNReal.ofReal ((1 - Real.cos x) / x ^ 2) := by
  sorry
