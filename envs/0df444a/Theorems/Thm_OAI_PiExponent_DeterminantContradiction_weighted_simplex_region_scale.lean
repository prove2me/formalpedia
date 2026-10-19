-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_region_scale
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_simplex_region_scale
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T02:59:05.951361+00:00
-- url     : https://prove2.me/theorems/2c52a110-1856-4795-9822-133c57824dcc
-- title:
--   Diagonal scaling of the weighted simplex region
-- statement:
--   For positive coordinate weights, the real-valued volume of the weighted simplex equals the standard simplex volume multiplied by the reciprocal of the product of the weights; this scaling identity also covers dimension zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion

open scoped BigOperators Topology
open OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.DeterminantContradiction.weighted_simplex_region_scale
    (m : ℕ) (w : Fin m → ℝ) (T : ℝ) (hw : ∀ i, 0 < w i) :
    ENNReal.toReal (MeasureTheory.volume (weightedSimplexRegion w T)) =
      (∏ i : Fin m, w i)⁻¹ * ENNReal.toReal (MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ T}) := by sorry
