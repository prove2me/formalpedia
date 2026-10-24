-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_normalization
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_normalization
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:14:12.247971+00:00
-- url     : https://prove2.me/theorems/800d0856-1eeb-4306-8dd7-d7979912035f
-- title:
--   Normalize a positive weighted simplex
-- statement:
--   For positive B and positive weights, dividing the weighted sum bound by B gives exactly the same region, expressed through the normalized coordinates. This is a pointwise equivalence using positivity of B and each weight.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_normalization
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i) (B : Real) (hB : 0 < B) :
    {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) ≤ B} =
      {x : Fin n → Real | (∀ i, 0 ≤ (w i / B) * x i) ∧
        (∑ i, (w i / B) * x i) ≤ 1} := by sorry
