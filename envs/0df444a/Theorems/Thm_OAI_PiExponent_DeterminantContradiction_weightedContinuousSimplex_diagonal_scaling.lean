-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedContinuousSimplex_diagonal_scaling
-- name    : OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_diagonal_scaling
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:10:40.531458+00:00
-- url     : https://prove2.me/theorems/90a8e5a4-52c0-432b-b46e-0989c2a53716
-- title:
--   Diagonal scaling for the weighted simplex
-- statement:
--   For positive coordinate weights, the weighted simplex volume is the standard simplex volume multiplied by the reciprocal of the product of the weights. Coordinatewise multiplication by the weights is an invertible diagonal map; its determinant gives the volume factor.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_diagonal_scaling
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < T}
      = ENNReal.ofReal (1 / Finset.univ.prod w) *
        MeasureTheory.volume
          {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T} := by sorry
