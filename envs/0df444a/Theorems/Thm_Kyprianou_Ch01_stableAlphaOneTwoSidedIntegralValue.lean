-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneTwoSidedIntegralValue
-- name    : Kyprianou.Ch01.stableAlphaOneTwoSidedIntegralValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:50:39.477244+00:00
-- url     : https://prove2.me/theorems/797ee0cb-0d21-4f24-97ac-1b90f98f06c6
-- title:
--   Exact two-sided alpha-one oscillatory Gamma integral from positive-kernel log phase
-- statement:
--   Combining the proved positive Cauchy Lévy kernel integral at xi and -xi with cpos,cneg yields the exact real π(cpos+cneg)|xi|/2 term, imaginary logarithmic skew (cpos-cneg)xi log|xi|, and a linear drift correction depending on a single absolute constant k. Valid for all real xi including zero.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, index one two-sided stable characteristic exponent integral.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Real Set Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneTwoSidedIntegralValue (cpos cneg : ℝ) :
    ∃ k : ℝ, ∀ xi : ℝ,
      let F : ℝ → ℂ := (fun z : ℝ =>
      ∫ r in Set.Ioi (0 : ℝ),
        ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
            Complex.I * (((z * r : ℝ) : ℂ)) *
              (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume)
      (cpos : ℂ) * F xi + (cneg : ℂ) * F (-xi) = (((Real.pi * (cpos + cneg) * |xi| / 2 : ℝ) : ℂ) +
        Complex.I * ((((cpos - cneg) * xi * Real.log |xi| : ℝ) : ℂ)) -
        Complex.I * ((((cpos - cneg) * k * xi : ℝ) : ℂ))) := by sorry
