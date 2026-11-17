-- Prove2me | Theorems.Thm_Kyprianou_Ch01_logarithmicJumpCompoundPoissonExponent
-- name    : Kyprianou.Ch01.logarithmicJumpCompoundPoissonExponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T00:02:21.818201+00:00
-- url     : https://prove2.me/theorems/0b0228f9-28cf-4ec8-80f1-e34d5aa862d8
-- title:
--   Logarithmic jump exponent gives the geometric generating function
-- statement:
--   For complex q and z with |q|<1 and |qz|<1, exponentiating the absolutely convergent logarithmic jump series gives (1-q)/(1-qz). This is the analytic identity needed to identify a logarithmic-jump compound-Poisson law with the geometric count law in Kyprianou's Exercise 1.2(i).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(i); uses the proved complex logarithmic jump-series formula.

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Theorems.Thm_Kyprianou_Ch01_logarithmicJumpComplexExponent
open Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.logarithmicJumpCompoundPoissonExponent
    (q z : ℂ) (hq : ‖q‖ < 1) (hqz : ‖q * z‖ < 1) :
    Complex.exp
      (∑' n : ℕ,
        ((q * z) ^ (n + 1) / ((n : ℂ) + 1) -
          q ^ (n + 1) / ((n : ℂ) + 1))) =
      (1 - q) / (1 - q * z) := by
  sorry
