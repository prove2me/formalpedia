-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_strictWeightedSimplex_unitBoxUnion_subset
-- name    : OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_unitBoxUnion_subset
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:11:39.202111+00:00
-- url     : https://prove2.me/theorems/dc3bff91-9048-4edc-aeed-319dcd5e9f46
-- title:
--   Boxes based at strict weighted simplex points lie in the expanded region
-- statement:
--   With positive weights, every unit box based at a strict weighted lattice point lies in the nonnegative weighted region whose height is increased by the sum of the weights.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Definitions.Def_OAI_PiExponent_DeterminantContradiction_UnitBoxes
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_unitBoxUnion_subset
    (n : ℕ) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (H : ℝ) (hH : 0 ≤ H) :
    unitBoxUnion (strictWeightedSimplex w H) ⊆
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧
        (∑ i, w i * x i) ≤ H + Finset.univ.sum w} := by sorry
