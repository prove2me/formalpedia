-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_strictWeightedSimplex_card_ge_shifted_volume_covered_by_boxes
-- name    : OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_card_ge_shifted_volume_covered_by_boxes
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:12:57.79141+00:00
-- url     : https://prove2.me/theorems/d46ba639-f2a3-471c-b8ba-02cb1f661580
-- title:
--   The shifted boxes cover the weighted simplex in volume
-- statement:
--   The nonnegative weighted simplex below height T has volume at most the volume of the union of unit boxes indexed by the shifted strict weighted simplex. For each point, coordinatewise floors give an index in that finite simplex, and the point belongs to its unit box.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_card_ge_shifted_volume_covered_by_boxes
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T) :
    ENNReal.toReal
      (MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < T})
      ≤ ENNReal.toReal
        (MeasureTheory.volume
          (⋃ a ∈ (strictWeightedSimplex w (T + Finset.univ.sum w) : Set (Fin n → Nat)),
            {x : Fin n → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1})) := by sorry
