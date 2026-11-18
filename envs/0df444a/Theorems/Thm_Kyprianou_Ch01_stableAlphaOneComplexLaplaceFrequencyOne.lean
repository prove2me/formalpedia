-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneComplexLaplaceFrequencyOne
-- name    : Kyprianou.Ch01.stableAlphaOneComplexLaplaceFrequencyOne
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T09:18:04.413305+00:00
-- url     : https://prove2.me/theorems/d4295856-d69d-4f40-af57-65c9685fdbde
-- title:
--   Damped complex exponential has a rational positive-half-line Laplace transform
-- statement:
--   For each positive damping a>0, integrating the complex function exp((-a+i)x) over positive real x yields 1/(a−i). This follows from the pinned Mathlib exponentially decaying complex improper integral. Taking real parts will evaluate the positive Laplace cosine transform needed to convert the index-one stable Lévy cosine kernel into 1/(1+a²).
-- source:
--   Kyprianou (2006), Chapter 1, stable index-one Lévy exponent; elementary complex Laplace transform.

import Mathlib
open MeasureTheory Complex Real Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneComplexLaplaceFrequencyOne
    (a : ℝ) (ha : 0 < a) :
    (∫ x in Set.Ioi (0 : ℝ),
      Complex.exp (((-(a : ℂ)) + Complex.I) * (x : ℂ))) =
      ((a : ℂ) - Complex.I)⁻¹ := by
  sorry
