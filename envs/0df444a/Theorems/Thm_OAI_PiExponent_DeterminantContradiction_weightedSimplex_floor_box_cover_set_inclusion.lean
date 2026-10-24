-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_floor_box_cover_set_inclusion
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_floor_box_cover_set_inclusion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:16:52.420988+00:00
-- url     : https://prove2.me/theorems/1acc66eb-d691-4865-83ad-f5956ae29b9e
-- title:
--   Floor boxes cover the contracted weighted simplex
-- statement:
--   Every point in the contracted simplex belongs to a unit box indexed by a feasible nonnegative integer vector.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_floor_box_cover_set_inclusion {m : Nat} (w : Fin m → Real) (R : Real) (hw : ∀ i, 0 < w i) (hR : ∑ i : Fin m, w i < R) : {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ R - ∑ i : Fin m, w i} ⊆ (⋃ n ∈ realWeightedSimplex w R, {x : Fin m → Real | ∀ i, (n i : Real) ≤ x i ∧ x i < (n i : Real) + 1}) := by sorry
