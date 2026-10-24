-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_floor_box_bound
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_floor_box_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:03:02.449243+00:00
-- url     : https://prove2.me/theorems/bbd50d9c-9992-4a47-b1e1-b38f428a549b
-- title:
--   Floor-box bound for a contracted weighted simplex
-- statement:
--   The real-valued volume of the contracted weighted simplex is at most the number of nonnegative integer vectors whose weighted sum is at most R.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_floor_box_bound {m : Nat} (w : Fin m → Real) (R : Real) (hw : ∀ i, 0 < w i) (hR : ∑ i : Fin m, w i < R) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ R - ∑ i : Fin m, w i}).toReal ≤
      ((realWeightedSimplex w R).card : Real) := by sorry
