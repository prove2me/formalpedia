-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexSlices_image
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexSlices_image
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:19:25.601848+00:00
-- url     : https://prove2.me/theorems/20664fa4-beb8-472e-b0f0-1025e5b223c2
-- title:
--   Identify a simplex slice with a coordinatewise image
-- statement:
--   For every nonnegative real `a`, the nonnegative simplex cut off at `a` is the image of the unit simplex under coordinatewise multiplication by `a`. This includes `a = 0` and dimension zero.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexSlices_image (n : Nat) (a : Real) (ha : 0 ≤ a) :
    {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
      (Finset.univ.sum fun i : Fin n => x i) ≤ a} =
    Set.image (fun y : Fin n → Real => fun i => a * y i)
      {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧
        (Finset.univ.sum fun i : Fin n => y i) ≤ 1} := by sorry
