-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_floor_box_cover_rhs_finite
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_floor_box_cover_rhs_finite
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:17:06.771472+00:00
-- url     : https://prove2.me/theorems/60f441e2-ac33-40c2-98f9-3e605ee02abb
-- title:
--   The feasible floor-box union has finite volume
-- statement:
--   The finite union of unit boxes indexed by the feasible simplex has finite Lebesgue volume.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_floor_box_cover_rhs_finite {m : Nat} (w : Fin m → Real) (R : Real) (hw : ∀ i, 0 < w i) (hR : ∑ i : Fin m, w i < R) : MeasureTheory.volume (⋃ n ∈ realWeightedSimplex w R, {x : Fin m → Real | ∀ i, (n i : Real) ≤ x i ∧ x i < (n i : Real) + 1}) ≠ ⊤ := by sorry
