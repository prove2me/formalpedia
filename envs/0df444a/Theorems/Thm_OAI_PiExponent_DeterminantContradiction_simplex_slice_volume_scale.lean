-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_slice_volume_scale
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_slice_volume_scale
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T21:14:33.229351+00:00
-- url     : https://prove2.me/theorems/10af2ae6-4206-4477-bc7c-efa3ddf06301
-- title:
--   Simplex volume scales under dilation
-- statement:
--   For each nonnegative cutoff a, dilation of the unit simplex gives the cutoff-a simplex and scales its m-dimensional volume by a^m. The zero-cutoff, positive-dimensional case is a singleton of volume zero; in dimension zero the identity is 1 = 1.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_slice_volume_scale (m : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (MeasureTheory.volume
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ a}).toReal =
      a ^ m * (MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ 1}).toReal := by sorry
