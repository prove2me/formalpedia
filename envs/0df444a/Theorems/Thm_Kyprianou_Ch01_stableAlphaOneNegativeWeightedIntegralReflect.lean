-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneNegativeWeightedIntegralReflect
-- name    : Kyprianou.Ch01.stableAlphaOneNegativeWeightedIntegralReflect
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:22:48.787731+00:00
-- url     : https://prove2.me/theorems/46fba133-ed1d-487d-ad3c-ebe6fdcd7f3e
-- title:
--   Reflect negative weighted compensated integral to positive radii
-- statement:
--   Change r to -r in the negative-halfline compensated Lebesgue integral; use the exact proved reflection of the compensated integrand, including cutoff.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, alpha=1 exact two-sided Levy measure decomposition.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneNegativeWeightedIntegralReflect
    (c xi : ℝ) :
    (∫ r in Set.Iio (0 : ℝ),
      (c * |r| ^ (-2 : ℝ)) • ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) =
    (∫ r in Set.Ioi (0 : ℝ),
      (c * r ^ (-2 : ℝ)) •
        ProbabilityTheory.levyCompensatedIntegrand (-xi) r ∂volume) := by sorry
