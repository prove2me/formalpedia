-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_floor_box_cover
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_floor_box_cover
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:07:54.667886+00:00
-- url     : https://prove2.me/theorems/c08bbf61-12f5-4b8d-a886-60fb250f4059
-- title:
--   Cover the contracted simplex by feasible floor boxes
-- statement:
--   The contracted weighted simplex has no greater volume than the union of the half-open unit boxes based at its feasible nonnegative integer vectors.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_floor_box_cover {m : Nat} (w : Fin m → Real) (R : Real) (hw : ∀ i, 0 < w i) (hR : ∑ i : Fin m, w i < R) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ R - ∑ i : Fin m, w i}).toReal ≤
      (MeasureTheory.volume (⋃ n ∈ realWeightedSimplex w R,
        {x : Fin m → Real | ∀ i, (n i : Real) ≤ x i ∧ x i < (n i : Real) + 1})).toReal := by sorry
