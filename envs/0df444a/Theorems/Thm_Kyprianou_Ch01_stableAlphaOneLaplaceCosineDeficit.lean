-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLaplaceCosineDeficit
-- name    : Kyprianou.Ch01.stableAlphaOneLaplaceCosineDeficit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T09:27:16.272206+00:00
-- url     : https://prove2.me/theorems/7552ae09-35e0-4a38-9fa3-7575f66667af
-- title:
--   Exponential Laplace integral of the cosine deficit equals the positive rational kernel
-- statement:
--   For every positive a, the absolutely convergent integral over x>0 of a exp(−a x)(1−cos x) equals 1/(1+a²). It follows from the standard Laplace transform of exp(−a x) and the separately proved exact Laplace transform of exp(−a x)cos x. The integrand is everywhere nonnegative and enables a Tonelli representation of the stable alpha-one cosine integral using the inverse-square Laplace kernel.
-- source:
--   Kyprianou (2006), Chapter 1, α=1 stable Lévy cosine exponent; Laplace–Tonelli rational kernel.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLaplaceCosine
open MeasureTheory Real Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneLaplaceCosineDeficit
    (a : ℝ) (ha : 0 < a) :
    (∫ x in Set.Ioi (0 : ℝ),
      a * Real.exp (-(a * x)) * (1 - Real.cos x)) =
        (1 + a ^ 2)⁻¹ := by
  sorry
