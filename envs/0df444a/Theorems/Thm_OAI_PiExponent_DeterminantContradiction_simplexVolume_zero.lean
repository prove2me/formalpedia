-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_zero
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T02:32:53.807998+00:00
-- url     : https://prove2.me/theorems/c559f017-46c9-4691-9ee2-7154ad96ffa8
-- title:
--   Zero-dimensional unit simplex volume
-- statement:
--   The zero-dimensional nonnegative unit simplex has real volume one. Its constraint set is the singleton zero-dimensional function space.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_zero :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ (1 : ℝ)}) = 1 := by sorry
