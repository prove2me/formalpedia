-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_slicing_fubini
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_slicing_fubini
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:15:21.146965+00:00
-- url     : https://prove2.me/theorems/b200d816-92f3-4ed1-97e3-a8a08fbea179
-- title:
--   Fubini formula for standard simplex slices
-- statement:
--   Slice the nonnegative (n+1)-simplex by its last coordinate t. For t in [0,1], the remaining coordinates form the n-simplex with sum at most 1 − t; outside that interval, the slice is empty. Fubini over the last coordinate yields the stated identity.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_slicing_fubini (n : Nat) :
    MeasureTheory.volume
        {y : Fin (n + 1) → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1} =
      ∫⁻ t in Set.Icc (0 : Real) 1,
        MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1 - t}
        ∂MeasureTheory.volume := by sorry
