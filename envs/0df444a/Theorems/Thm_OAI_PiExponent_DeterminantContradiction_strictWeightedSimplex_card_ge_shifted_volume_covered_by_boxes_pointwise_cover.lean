-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_strictWeightedSimplex_card_ge_shifted_volume_covered_by_boxes_pointwise_cover
-- name    : OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_card_ge_shifted_volume_covered_by_boxes_pointwise_cover
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T11:54:07.966089+00:00
-- url     : https://prove2.me/theorems/43b8b086-13b6-4bb9-aaf5-08de35b9da95
-- title:
--   Floor indices cover the weighted simplex pointwise
-- statement:
--   For every point in the nonnegative weighted simplex, coordinatewise natural floors give an index in the shifted strict weighted simplex and a unit box containing the point. This is the main geometric step removed from the parent. A proof route is to use the natural floor bounds, multiply the lower bounds by the positive weights, and sum; then show the resulting index satisfies both the strict weighted-sum filter and the coordinate cutoff in realWeightedSimplex. The zero-dimensional case has the unique empty index and satisfies the same statement.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_card_ge_shifted_volume_covered_by_boxes_pointwise_cover
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T)
    (x : Fin n → Real)
    (hx : (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < T) :
    ∃ a : Fin n → Nat,
      a ∈ strictWeightedSimplex w (T + Finset.univ.sum w) ∧
      ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1 := by sorry
