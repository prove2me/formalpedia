-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_diagonal_map_volume
-- name    : OAI.PiExponent.DeterminantContradiction.diagonal_map_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:17:39.672993+00:00
-- url     : https://prove2.me/theorems/be4f8081-8e72-4c29-aa4f-62d2118b0c65
-- title:
--   Volume scaling under the diagonal map
-- statement:
--   The coordinatewise map multiplying each coordinate by its positive weight scales the real-valued volume of the weighted simplex by the product of the weights.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion

open scoped BigOperators Topology
open OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.DeterminantContradiction.diagonal_map_volume (m : ℕ) (w : Fin m → ℝ) (T : ℝ) (hw : ∀ i, 0 < w i) : ENNReal.toReal (MeasureTheory.volume ((fun x i => w i * x i) '' weightedSimplexRegion w T)) = (∏ i : Fin m, w i) * ENNReal.toReal (MeasureTheory.volume (weightedSimplexRegion w T)) := by sorry
