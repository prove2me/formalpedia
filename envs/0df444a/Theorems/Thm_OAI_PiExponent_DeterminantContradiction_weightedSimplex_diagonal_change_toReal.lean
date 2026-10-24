-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_diagonal_change_toReal
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_diagonal_change_toReal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:49:12.04044+00:00
-- url     : https://prove2.me/theorems/eac61d1c-8168-4350-95fc-e42e9e658196
-- title:
--   Diagonal scaling for a weighted simplex
-- statement:
--   For positive coordinate weights, the weighted simplex volume is the unweighted simplex volume divided by the product of the weights, by the invertible diagonal coordinate map.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_diagonal_change_toReal {m : Nat} (w : Fin m → Real) (A : Real)
    (hw : ∀ i, 0 < w i) (hA : 0 < A) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧
      ∑ i : Fin m, w i * x i ≤ A}).toReal =
      (MeasureTheory.volume {y : Fin m → Real | (∀ i : Fin m, 0 ≤ y i) ∧
        ∑ i : Fin m, y i ≤ A}).toReal / ∏ i : Fin m, w i := by sorry
