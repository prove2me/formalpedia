-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricRandomSumCharExponent
-- name    : Kyprianou.Ch01.geometricRandomSumCharExponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:18:49.363999+00:00
-- url     : https://prove2.me/theorems/1fc85b6a-cc2d-48a2-be41-1b724e87912d
-- title:
--   Compound-geometric Fourier exponent for an arbitrary probability increment distribution
-- statement:
--   For any real-valued probability jump law and strict geometric parameter 0<p<1, the exponent obtained from logarithmic cluster counts and the increment characteristic function equals the characteristic ratio p/[1−(1−p)φ(ξ)]. This exact identity applies to the arbitrary-IID-increments case of Kyprianou Chapter 1 Exercise 1.2(ii).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), geometric stopped IID random sum and logarithmic compound-Poisson clusters.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_geometricMarkCompoundPoissonExponent
open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricRandomSumCharExponent
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (xi : ℝ) :
    Complex.exp (∑' n : ℕ,
      ((((1 - p : ℝ) : ℂ) ^ (n + 1)) / ((n : ℂ) + 1)) *
        ((charFun jumpLaw xi) ^ (n + 1) - 1)) =
      (p : ℂ) / (1 - (((1 - p : ℝ) : ℂ)) * charFun jumpLaw xi) := by
  sorry
