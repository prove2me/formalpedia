-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedContinuousSimplex_standardSimplex_volume
-- name    : OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_standardSimplex_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:10:19.479824+00:00
-- url     : https://prove2.me/theorems/8584d107-a254-4d2b-9430-98f41f12b48e
-- title:
--   Volume of the standard continuous simplex
-- statement:
--   The volume of the nonnegative simplex whose coordinate sum is strictly below positive height T is T to the dimension divided by the dimension factorial. This covers dimension zero, where both sides are one.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_standardSimplex_volume
    (n : Nat) (T : Real) (hT : 0 < T) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T}
      = ENNReal.ofReal (T ^ n / (n.factorial : Real)) := by sorry
