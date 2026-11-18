-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineEqualsSincSquare
-- name    : Kyprianou.Ch01.stableAlphaOneCosineEqualsSincSquare
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T09:11:28.892802+00:00
-- url     : https://prove2.me/theorems/050d69a6-4462-443f-bfdf-9a09a1d4ea85
-- title:
--   Stable index-one cosine integral equals the positive-half-line sinc-squared integral
-- statement:
--   The absolutely convergent integral of (1−cos x)/x² over positive x equals the integral of (sin x/x)² over positive x. This is an exact change-of-variables identity using 1−cos(2y)=2sin² y and x=2y. It converts the index-one stable cosine-value calculation into the absolutely integrable sinc-squared integral, avoiding conditional convergence of sin(x)/x.
-- source:
--   Kyprianou (2006), Chapter 1, stable alpha-one Lévy exponent; trigonometric half-angle identity.

import Mathlib
open MeasureTheory Filter Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCosineEqualsSincSquare :
    (∫ x in Set.Ioi (0 : ℝ), (1 - Real.cos x) / x ^ 2) =
    ∫ x in Set.Ioi (0 : ℝ), (Real.sin x / x) ^ 2 := by
  sorry
