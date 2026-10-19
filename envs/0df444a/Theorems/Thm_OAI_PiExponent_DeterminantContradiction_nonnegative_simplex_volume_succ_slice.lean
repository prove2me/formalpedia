-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_nonnegative_simplex_volume_succ_slice
-- name    : OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume_succ_slice
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:09:31.188355+00:00
-- url     : https://prove2.me/theorems/36ad3d5c-ef02-4049-9428-8b936fb9282e
-- title:
--   Slice identity for nonnegative simplex volume
-- statement:
--   The volume of the nonnegative simplex at cutoff U is the integral, over its last coordinate t from 0 to U, of the volumes of the remaining-coordinate slices at cutoff U − t.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume_succ_slice
    (m : ℕ) (U : ℝ) (hU : 0 ≤ U) :
    (MeasureTheory.volume
      {x : Fin (m + 1) → ℝ |
        (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ U}).toReal =
      ∫ t in (0 : ℝ)..U,
        (MeasureTheory.volume
          {x : Fin m → ℝ |
            (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ U - t}).toReal := by sorry
