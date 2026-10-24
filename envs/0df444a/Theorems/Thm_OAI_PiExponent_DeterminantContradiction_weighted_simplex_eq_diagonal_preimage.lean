-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_eq_diagonal_preimage
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_simplex_eq_diagonal_preimage
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:52:54.65179+00:00
-- url     : https://prove2.me/theorems/4183a7ff-a795-4ec1-baaa-d5b493631fe6
-- title:
--   Weighted simplex as a diagonal preimage
-- statement:
--   With positive weights, a point belongs to the weighted simplex exactly when its coordinatewise diagonal image belongs to the ordinary simplex.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weighted_simplex_eq_diagonal_preimage {m : Nat} (w : Fin m → Real) (A : Real)
    (hw : ∀ i, 0 < w i) :
    {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A} =
      (fun x : Fin m → Real => fun i => w i * x i) ⁻¹' {y : Fin m → Real |
        (∀ i : Fin m, 0 ≤ y i) ∧ ∑ i : Fin m, y i ≤ A} := by sorry
