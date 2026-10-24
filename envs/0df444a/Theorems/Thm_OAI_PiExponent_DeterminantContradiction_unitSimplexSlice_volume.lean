-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexSlice_volume
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:15:47.602921+00:00
-- url     : https://prove2.me/theorems/2f6d7a2b-d6ab-4765-88ee-e76e3b5a3ea6
-- title:
--   Volume of a truncated unit simplex
-- statement:
--   For t in [0,1], the n-dimensional nonnegative simplex cut off by sum xᵢ ≤ 1 − t has volume (1 − t)^n/n!.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_volume (n : Nat) (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ 1 - t} =
    ENNReal.ofReal ((1 - t) ^ n / (n.factorial : Real)) := by sorry
