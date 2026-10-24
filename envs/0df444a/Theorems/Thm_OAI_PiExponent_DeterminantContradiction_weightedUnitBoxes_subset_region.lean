-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedUnitBoxes_subset_region
-- name    : OAI.PiExponent.DeterminantContradiction.weightedUnitBoxes_subset_region
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:35:10.18288+00:00
-- url     : https://prove2.me/theorems/4f9a9e71-4982-490a-ad43-75151719f06f
-- title:
--   The unit boxes lie in the enlarged weighted region
-- statement:
--   For positive coordinate weights, every point in each half-open unit box based at a lattice point of the weighted simplex has nonnegative coordinates and weighted sum at most `B + ∑ᵢ wᵢ`.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedUnitBoxes_subset_region {m : Nat} (w : Fin m → Real) (B : Real)
    (hw : ∀ i, 0 < w i) :
    (⋃ a ∈ OAI.PiExponent.realWeightedSimplex w B,
      {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1}) ⊆
      {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧
        ∑ i : Fin m, w i * x i ≤ B + ∑ i : Fin m, w i} := by sorry
