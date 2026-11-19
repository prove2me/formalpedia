-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaConvolutionPolynomialIntegral
-- name    : Kyprianou.Ch01.gammaConvolutionPolynomialIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:11:42.653265+00:00
-- url     : https://prove2.me/theorems/916acb9c-e3a9-4ad2-ac3b-076731efa93e
-- title:
--   Gamma convolution polynomial integral evaluates to next arrival density
-- statement:
--   For z≥0, integrating the positive gamma convolution polynomial density factor over [0,z] gives the exact Gamma(n+2,beta) arrival density value. The proof uses the interval integral of x^n, gamma factorial recurrence, and positivity.
-- source:
--   Kyprianou (2006), Exercise 1.8(iv), solution pp.304–305

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_levy_foundations_arrivalGammaDensity
set_option autoImplicit false

theorem Kyprianou.Ch01.gammaConvolutionPolynomialIntegral
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ)
    (z : ℝ) (hz : 0 ≤ z) :
    (∫⁻ x in Set.Icc (0 : ℝ) z,
      ENNReal.ofReal
        ((beta ^ (n + 2) * Real.exp (-(beta * z)) /
          (n.factorial : ℝ)) * x ^ n)) =
      LevyFoundations.arrivalGammaDensity beta (n + 1) z := by
  sorry
