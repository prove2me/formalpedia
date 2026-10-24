-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_volume_unitSimplex_image
-- name    : OAI.PiExponent.DeterminantContradiction.volume_unitSimplex_image
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:21:11.388212+00:00
-- url     : https://prove2.me/theorems/efb0dc75-181c-430b-b60d-b697cd5a546b
-- title:
--   Volume of a dilated unit simplex
-- statement:
--   The image of the unit simplex under coordinatewise multiplication by a nonnegative scalar `a` has volume equal to the unit simplex volume times `a^n`, including the zero scalar and zero-dimensional cases.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.volume_unitSimplex_image (n : Nat) (a : Real) (ha : 0 ≤ a) :
    MeasureTheory.volume
      (Set.image (fun y : Fin n → Real => fun i => a * y i)
        {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧
          (Finset.univ.sum fun i : Fin n => y i) ≤ 1}) =
    MeasureTheory.volume
      {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧
        (Finset.univ.sum fun i : Fin n => y i) ≤ 1} *
      ENNReal.ofReal (a ^ n) := by sorry
