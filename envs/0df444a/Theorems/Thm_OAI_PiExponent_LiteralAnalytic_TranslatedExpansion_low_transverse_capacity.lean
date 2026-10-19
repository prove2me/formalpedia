-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_low_transverse_capacity
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.low_transverse_capacity
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T10:04:01.246636+00:00
-- url     : https://prove2.me/theorems/7cf1a6cf-3138-498b-8c65-68750c91e4d0
-- title:
--   Low-weight indices inject into the low simplex
-- statement:
--   The cutoff indices inject into the weighted simplex at height $(d.base.A)H$ by sending each mapped finitely supported exponent vector to its underlying function.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.low_transverse_capacity {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    (((Finset.univ : Finset (indices d H)).filter
      (fun a => translatedIndexWeight d a ≤ (d.base.A : ℝ) * H)).card : ℝ) ≤
        (lowIndexCount d H : ℝ) := by sorry
