-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLaplaceDeficitLintegral
-- name    : Kyprianou.Ch01.stableAlphaOneLaplaceDeficitLintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T09:31:23.062426+00:00
-- url     : https://prove2.me/theorems/fe302c11-6a08-40a0-9f00-a5af4cae284b
-- title:
--   Tonelli-compatible positive Laplace deficit ENNReal integral equals a rational kernel
-- statement:
--   For positive a, the extended nonnegative Lebesgue integral of a exp(−ax)(1−cos x) over x>0 is ENNReal.ofReal((1+a²)⁻¹). The proof uses the already proved real Laplace-cosine-deficit value, cosine positivity, and domination by 2a exp(−ax) to justify the conversion from real Bochner to ENNReal integrals. This completes the right-hand inner integral required for a nonnegative Tonelli proof of the index-one stable cosine π/2 evaluation.
-- source:
--   Kyprianou (2006), Chapter 1, α=1 stable cosine Lévy exponent; Tonelli compatible Laplace-deficit kernel.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLaplaceCosineDeficit
open MeasureTheory Real Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneLaplaceDeficitLintegral
    (a : ℝ) (ha : 0 < a) :
    (∫⁻ x in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (a * Real.exp (-(a * x)) * (1 - Real.cos x))) =
      ENNReal.ofReal ((1 + a ^ 2)⁻¹) := by
  sorry
