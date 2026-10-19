-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_region_card_bound
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_simplex_region_card_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T02:53:37.151295+00:00
-- url     : https://prove2.me/theorems/e1d89945-0734-4b1c-99bb-c3326946cd30
-- title:
--   Simplex volume bounded by its lattice count
-- statement:
--   The real-valued volume of the nonnegative weighted simplex is bounded by the number of admissible nonnegative integer vectors, under positive weights and a nonnegative cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_WeightedSimplexRegion

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.DeterminantContradiction.weighted_simplex_region_card_bound
    (m : ℕ) (w : Fin m → ℝ) (T : ℝ)
    (hw : ∀ i, 0 < w i) (hT : 0 ≤ T) :
    ENNReal.toReal (MeasureTheory.volume (weightedSimplexRegion w T)) ≤
      ((OAI.PiExponent.realWeightedSimplex w T).card : ℝ) := by sorry
