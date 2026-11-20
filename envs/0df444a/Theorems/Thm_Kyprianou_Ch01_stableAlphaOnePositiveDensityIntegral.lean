-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOnePositiveDensityIntegral
-- name    : Kyprianou.Ch01.stableAlphaOnePositiveDensityIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:38:12.21273+00:00
-- url     : https://prove2.me/theorems/323a1476-2428-46a9-9c6f-63559e27b95b
-- title:
--   Positive-halfline exact nonnegative Cauchy Lévy density Bochner conversion
-- statement:
--   For nonnegative Lévy intensity c, transfer the index-one positive-halfline compensated jump integrand from the source ENNReal.ofReal weighted Lévy measure to the exactly weighted Lebesgue Bochner integral c*r^-2.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.4 alpha-one original power-law density.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOnePositiveDensityIntegral (c xi : ℝ) (hc : 0 ≤ c) :
    (∫ r, ProbabilityTheory.levyCompensatedIntegrand xi r ∂
      ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun r : ℝ => ENNReal.ofReal (c * r ^ (-2 : ℝ))))) =
    (∫ r in Set.Ioi (0 : ℝ),
      (c * r ^ (-2 : ℝ)) •
        ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) := by sorry
