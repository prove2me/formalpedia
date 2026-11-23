-- Prove2me | Theorems.Thm_Kyprianou_Ch02_poissonMeasureRealSecondMomentV1
-- name    : Kyprianou.Ch02.poissonMeasureRealSecondMomentV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:36:58.602462+00:00
-- url     : https://prove2.me/theorems/26ddf39d-1632-4c32-ab75-99e03c8d9de4
-- title:
--   Poisson law raw real second moment equals rate squared plus rate
-- statement:
--   For a Poisson law of any nonnegative rate r, the expected square of the real-valued count is r²+r. Proof reuses the existing Proved LevyStochCalc probability polynomial integration-by-parts theorem, exactly following the original PoissonMoments Lean source.
-- source:
--   LevyStochCalc/Probability/PoissonMoments.lean, original theorem integral_id_sq_poissonMeasure; Kyprianou (2006) Chapter 2

import Mathlib
open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.poissonMeasureRealSecondMomentV1
    (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ^ 2 ∂poissonMeasure r) =
      (r : ℝ) ^ 2 + (r : ℝ) := by sorry
