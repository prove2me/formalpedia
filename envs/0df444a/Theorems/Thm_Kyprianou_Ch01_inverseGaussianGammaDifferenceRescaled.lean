-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianGammaDifferenceRescaled
-- name    : Kyprianou.Ch01.inverseGaussianGammaDifferenceRescaled
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:50:34.750301+00:00
-- url     : https://prove2.me/theorems/6fe7d89c-61bb-45de-a006-9a460e7eb99f
-- title:
--   Complex Gamma half-index exponential difference normalised by inverse Gaussian square-root density
-- statement:
--   Specialise the proved strict-left complex Gamma difference to alpha=1/2 and u=-b²/2, v=-b²/2+i theta, then multiply by the exact inverse Gaussian constant 1/sqrt(2pi).
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.6(ii) original inverse Gaussian jump exponent.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianGammaDifferenceRescaled
    (b : ℝ) (hb : 0 < b) (theta : ℝ) :
    (((1 / Real.sqrt (2 * Real.pi) : ℝ)) : ℂ) * (∫ r in Set.Ioi (0 : ℝ),
        (Complex.exp (((-(b ^ 2 / 2) : ℝ) : ℂ) * (r : ℂ)) - Complex.exp ((((-(b ^ 2 / 2) : ℝ) : ℂ) +
            Complex.I * (theta : ℂ)) * (r : ℂ))) *
          ((r ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) ∂volume) =
    (((Real.Gamma (-(1 / 2 : ℝ)) / Real.sqrt (2 * Real.pi) : ℝ) : ℂ)) *
      (Complex.exp (((1 / 2 : ℝ) : ℂ) *
          Complex.log (((b ^ 2 / 2 : ℝ) : ℂ))) - Complex.exp (((1 / 2 : ℝ) : ℂ) *
          Complex.log ((((b ^ 2 / 2 : ℝ) : ℂ) -
            Complex.I * (theta : ℂ))))) := by sorry
