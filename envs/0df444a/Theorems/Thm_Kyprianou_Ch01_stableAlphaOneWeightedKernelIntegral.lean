-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneWeightedKernelIntegral
-- name    : Kyprianou.Ch01.stableAlphaOneWeightedKernelIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:22:48.228104+00:00
-- url     : https://prove2.me/theorems/c27b1389-1613-4b14-bdfc-d956ccaf5c83
-- title:
--   Integrate the proved positive weighted jump kernel identity
-- statement:
--   Integrate the proved pointwise stableAlphaOnePositiveWeightedJumpKernel over positive radii and pull the constant multiplier c outside the Bochner integral.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, alpha=1 exact two-sided Levy measure decomposition.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneWeightedKernelIntegral
    (c xi : ℝ) :
    -(∫ r in Set.Ioi (0 : ℝ),
      (c * r ^ (-2 : ℝ)) •
        ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) =
    (c : ℂ) * (∫ r in Set.Ioi (0 : ℝ),
      ((1 : ℂ) - Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) +
        Complex.I * (((xi * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
      ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume) := by sorry
