-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_region_volume
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_simplex_region_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T02:53:04.29264+00:00
-- url     : https://prove2.me/theorems/2d10c791-bb88-4c63-8575-5f74b18a3c2c
-- title:
--   Real volume formula for the weighted simplex
-- statement:
--   The real-valued measure of the nonnegative weighted simplex is its standard volume formula, retaining the positive-weight and nonnegative-cutoff hypotheses, including the zero-dimensional and zero-cutoff cases.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.DeterminantContradiction.weighted_simplex_region_volume
    (m : ℕ) (w : Fin m → ℝ) (T : ℝ)
    (hw : ∀ i, 0 < w i) (hT : 0 ≤ T) :
    ENNReal.toReal (MeasureTheory.volume (weightedSimplexRegion w T)) =
      T ^ m / ((Nat.factorial m : ℝ) * ∏ i : Fin m, w i) := by sorry
