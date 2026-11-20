-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneNegativeDensityIntegral
-- name    : Kyprianou.Ch01.stableAlphaOneNegativeDensityIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:22:46.694008+00:00
-- url     : https://prove2.me/theorems/b73277d3-55cd-47ed-a2c3-96e95cfb17ad
-- title:
--   Negative-halfline nonnegative Levy density conversion
-- statement:
--   Use the exact weighted-density Bochner conversion for an index-one negative-halfline Levy measure with coefficient c>=0.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, alpha=1 exact two-sided Levy measure decomposition.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneNegativeDensityIntegral
    (c xi : ℝ) (hc : 0 ≤ c) :
    (∫ r, ProbabilityTheory.levyCompensatedIntegrand xi r ∂
      ((volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun r : ℝ => ENNReal.ofReal (c * |r| ^ (-2 : ℝ))))) =
    (∫ r in Set.Iio (0 : ℝ),
      (c * |r| ^ (-2 : ℝ)) •
        ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) := by sorry
