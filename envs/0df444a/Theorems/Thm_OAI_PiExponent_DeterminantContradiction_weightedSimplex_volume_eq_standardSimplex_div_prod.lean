-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_volume_eq_standardSimplex_div_prod
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_eq_standardSimplex_div_prod
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:45:35.174335+00:00
-- url     : https://prove2.me/theorems/d435d312-ee46-40ca-9b79-760a2aebe158
-- title:
--   Diagonal scaling of the weighted simplex
-- statement:
--   For nonnegative A and positive coordinate weights, the weighted simplex volume is the standard simplex volume divided by the product of the weights; the statement also covers dimension zero.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_eq_standardSimplex_div_prod {m : Nat} (w : Fin m → Real) (A : Real) (hw : ∀ i, 0 < w i) (hA : 0 ≤ A) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A}).toReal =
      ((MeasureTheory.volume {y : Fin m → Real | (∀ i, 0 ≤ y i) ∧ ∑ i : Fin m, y i ≤ A}).toReal) / ∏ i : Fin m, w i := by sorry
