-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_factor_bounds_index_geometry
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_index_geometry
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T09:43:26.347173+00:00
-- url     : https://prove2.me/theorems/2803ccf1-a7bc-455e-a929-a9621d786f93
-- title:
--   Geometric bounds for translated indices
-- statement:
--   For positive height, the low-index count is positive, every translated index has nonnegative weight, and the number of indices of weight at most $A H$ is bounded by the low-index count.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_index_geometry
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < (lowIndexCount d H : ℝ) ∧
    (∀ a : indices d H, 0 ≤ translatedIndexWeight d a) ∧
    (((Finset.univ : Finset (indices d H)).filter
      (fun a => translatedIndexWeight d a ≤ (d.base.A : ℝ) * H)).card : ℝ) ≤
        (lowIndexCount d H : ℝ) := by sorry
