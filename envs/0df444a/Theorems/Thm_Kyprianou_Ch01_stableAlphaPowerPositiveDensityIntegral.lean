-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaPowerPositiveDensityIntegral
-- name    : Kyprianou.Ch01.stableAlphaPowerPositiveDensityIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:37:01.124422+00:00
-- url     : https://prove2.me/theorems/c4aecfeb-0989-4571-b791-82477d5159cc
-- title:
--   Positive-halfline stable power-law Lévy density integral conversion for arbitrary exponent
-- statement:
--   For real stable index alpha and c>=0, integrate the original compensated jump factor against the exact Positive-halfline power-law Levy withDensity measure as a real weighted positive/negative halfline Bochner integral. This generalises the already-Proved alpha-one density conversion without modifying the cutoff.
-- source:
--   Kyprianou (2006), Exercise 1.4, stable two-sided power-law original Lévy measure.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaPowerPositiveDensityIntegral
    (alpha c xi : ℝ) (hc : 0 ≤ c) :
    (∫ r, ProbabilityTheory.levyCompensatedIntegrand xi r ∂
      ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun r : ℝ => ENNReal.ofReal (c * r ^ (-alpha - 1))))) =
    (∫ r in Set.Ioi (0 : ℝ),
      (c * r ^ (-alpha - 1)) •
        ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) := by sorry
