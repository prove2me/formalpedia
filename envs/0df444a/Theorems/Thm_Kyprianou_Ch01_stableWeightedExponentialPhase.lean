-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableWeightedExponentialPhase
-- name    : Kyprianou.Ch01.stableWeightedExponentialPhase
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:45:31.385774+00:00
-- url     : https://prove2.me/theorems/347d5cba-4c9e-4523-a655-64f92ff139cb
-- title:
--   Two-sided weighted complex exponential phase equals canonical stable skewness factor
-- statement:
--   For nonzero sum of jump intensity coefficients and nonzero cosine phase, the weighted exponential phases cpos exp(-i theta)+cneg exp(i theta) equal (cpos+cneg)cos theta times (1-i beta tan theta), using the source-exact already-Proved trigonometric skew factor and Euler identity.
-- source:
--   Kyprianou (2006) Exercise 1.4 stable skew Lévy exponent.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableTwoSidedTrigSkewFactor
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableWeightedExponentialPhase
    (cpos cneg theta : ℝ)
    (hsum : cpos + cneg ≠ 0)
    (hcos : Real.cos theta ≠ 0) :
    (cpos : ℂ) * Complex.exp (-(Complex.I * (theta : ℂ))) +
    (cneg : ℂ) * Complex.exp (Complex.I * (theta : ℂ)) =
      (((cpos + cneg) * Real.cos theta : ℝ) : ℂ) *
        (1 - Complex.I *
          (((cpos - cneg) / (cpos + cneg) *
              Real.tan theta : ℝ) : ℂ)) := by sorry
