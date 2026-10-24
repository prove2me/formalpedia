-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_strictWeightedSimplex_shifted_boxes_volume_le_card
-- name    : OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_shifted_boxes_volume_le_card
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:13:26.86098+00:00
-- url     : https://prove2.me/theorems/35c4c24d-e54d-4d87-b673-66b2b1f640d6
-- title:
--   The shifted unit boxes have volume at most their index count
-- statement:
--   The volume of a finite union of coordinatewise half-open unit boxes is at most the number of boxes. Finite-union subadditivity and the unit volume of each box give the bound, including when n is zero.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_shifted_boxes_volume_le_card
    (n : Nat) (w : Fin n → Real) (T : Real) :
    ENNReal.toReal
      (MeasureTheory.volume
        (⋃ a ∈ (strictWeightedSimplex w (T + Finset.univ.sum w) : Set (Fin n → Nat)),
          {x : Fin n → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1}))
      ≤ ((strictWeightedSimplex w (T + Finset.univ.sum w)).card : Real) := by sorry
