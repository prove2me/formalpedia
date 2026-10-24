-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_strictWeightedSimplex_card_ge_volume
-- name    : OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_card_ge_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:54:57.735297+00:00
-- url     : https://prove2.me/theorems/cf8c5e7e-88fc-4d27-b28f-7afd730be0e5
-- title:
--   Strict weighted simplex count dominates the continuous simplex volume
-- statement:
--   For positive weights and positive cutoff, the volume of the nonnegative continuous weighted simplex is at most the number of nonnegative integer vectors whose weighted sum is strictly below the cutoff. Coordinatewise floors place every point of the continuous simplex in a unit box based at such an integer vector; the boxes are disjoint and have volume one.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_card_ge_volume
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < T}
      ≤ (strictWeightedSimplex w T).card := by sorry
