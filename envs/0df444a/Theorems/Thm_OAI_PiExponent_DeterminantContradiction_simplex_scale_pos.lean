-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_scale_pos
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_scale_pos
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T20:21:08.232713+00:00
-- url     : https://prove2.me/theorems/ded4ad24-628d-4bfd-ad01-73491703cd1c
-- title:
--   Homogeneity of the simplex at positive scale
-- statement:
--   For a strictly positive cutoff U, scaling every coordinate of the unit simplex by U multiplies its volume by U raised to the dimension. This removes the nondegenerate change-of-variables argument from the parent; prove it using the pinned Mathlib linear-map volume scaling theorem, the determinant of scalar multiplication, and the image of the unit simplex. The remaining core obligation is this positive-scale change-of-variables calculation.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_scale_pos (k : ℕ) (U : ℝ)
    (hU : 0 < U) :
    (MeasureTheory.volume
      {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ U}).toReal =
      (U ^ k) * (MeasureTheory.volume
        {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ 1}).toReal := by sorry
