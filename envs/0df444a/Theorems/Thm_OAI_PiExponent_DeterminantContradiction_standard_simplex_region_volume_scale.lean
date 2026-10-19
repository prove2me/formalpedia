-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_region_volume_scale
-- name    : OAI.PiExponent.DeterminantContradiction.standard_simplex_region_volume_scale
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:14:30.279145+00:00
-- url     : https://prove2.me/theorems/11192364-b4fa-425e-ba7a-f1acfbe00ecb
-- title:
--   Scaling the standard simplex region
-- statement:
--   For a nonnegative cutoff T, the simplex region’s volume is T to the m times the unit simplex volume. The statement covers T = 0 and m = 0.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.standard_simplex_region_volume_scale
    (m : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ T}) =
      T ^ m * ENNReal.toReal (MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ (1 : ℝ)}) := by sorry
