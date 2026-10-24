-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_diagonalScaling_image_weighted_eq_standardSimplex
-- name    : OAI.PiExponent.DeterminantContradiction.diagonalScaling_image_weighted_eq_standardSimplex
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:56:55.532379+00:00
-- url     : https://prove2.me/theorems/ba016d4c-60db-4893-ab03-8b556f13bded
-- title:
--   Diagonal image of the weighted simplex
-- statement:
--   Positive diagonal scaling maps the weighted simplex onto the standard simplex. In the reverse direction, use the coordinatewise inverse; positivity preserves nonnegativity. The statement also holds for dimension zero and at `A = 0`.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.diagonalScaling_image_weighted_eq_standardSimplex {m : Nat} (w : Fin m → Real) (A : Real) (hw : ∀ i, 0 < w i) (hA : 0 ≤ A) :
    (fun x : Fin m → Real => fun i => w i * x i) ''
        {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A} =
      {y : Fin m → Real | (∀ i, 0 ≤ y i) ∧ ∑ i : Fin m, y i ≤ A} := by sorry
