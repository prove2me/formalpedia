-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_eq_scaledSliceIntegral
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_scaledSliceIntegral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T02:17:24.157138+00:00
-- url     : https://prove2.me/theorems/557f619c-54c9-4606-ae20-3142e847b1ce
-- title:
--   Simplex volume from scaled slices
-- statement:
--   Express the real volume of the (n+1)-dimensional unit simplex as the real volume of the n-dimensional unit simplex times the real lintegral of the scaled-slice density over t.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_scaledSliceIntegral (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ (1 : ℝ)}) =
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) *
      ENNReal.toReal (∫⁻ t : ℝ,
        (if 0 ≤ t ∧ t ≤ 1 then ENNReal.ofReal (1 - t) ^ n else 0)
        ∂MeasureTheory.volume) := by sorry
