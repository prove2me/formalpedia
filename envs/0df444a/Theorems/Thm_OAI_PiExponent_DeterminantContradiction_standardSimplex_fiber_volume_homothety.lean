-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_fiber_volume_homothety
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_fiber_volume_homothety
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:19:48.950846+00:00
-- url     : https://prove2.me/theorems/fd91b190-d0c6-4b37-b937-62e9faa0619c
-- title:
--   Volume of a dilated standard simplex fiber
-- statement:
--   For any nonnegative radius, the volume of the nonnegative coordinate simplex cut off by coordinate sum at most that radius is the unit simplex volume multiplied by the radius to the dimension.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_fiber_volume_homothety (n : Nat) (r : Real) (hr : 0 ≤ r) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
    ENNReal.ofReal r ^ n *
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} := by sorry
