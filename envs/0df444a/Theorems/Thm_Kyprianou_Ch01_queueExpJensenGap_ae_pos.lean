-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueExpJensenGap_ae_pos
-- name    : Kyprianou.Ch01.queueExpJensenGap_ae_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T11:26:32.565897+00:00
-- url     : https://prove2.me/theorems/41674916-713e-4d52-afd6-7d531a96c9fd
-- title:
--   Positive strict Jensen exponential gap almost surely for nondegenerate claim sizes
-- statement:
--   On a distribution supported on positive sizes, strict convexity of the real exponential gives a strictly positive Jensen gap almost surely for distinct parameters and strictly positive convex weights.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.9(i), positive-claim exponential transform convexity

import Mathlib
open MeasureTheory Set
set_option autoImplicit false

theorem Kyprianou.Ch01.queueExpJensenGap_ae_pos
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (u v : ℝ) (huv : u ≠ v)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    ∀ᵐ z ∂F,
      0 < (1 - Real.exp (-(a * u + b * v) * z)) -
        (a * (1 - Real.exp (-u * z)) +
         b * (1 - Real.exp (-v * z))) := by sorry
