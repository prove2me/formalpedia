-- Prove2me | Theorems.Thm_OAI_PiExponent_Polynomials_realWeightedSimplex_map_filter_card_le
-- name    : OAI.PiExponent.Polynomials.realWeightedSimplex_map_filter_card_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T13:11:00.765571+00:00
-- url     : https://prove2.me/theorems/302ca21b-473a-4e08-9706-3fb42967df3f
-- title:
--   Weighted simplex cutoff capacity
-- statement:
--   For positive real weights, the elements of a mapped weighted simplex whose weighted sum is at most a cutoff inject into the weighted simplex at that cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains

open scoped BigOperators
open OAI.PiExponent

theorem OAI.PiExponent.Polynomials.realWeightedSimplex_map_filter_card_le {m : ℕ} (w : Fin m → ℝ) (H T : ℝ) (hw : ∀ i, 0 < w i) :
    (((Finset.univ : Finset ((OAI.PiExponent.realWeightedSimplex w H).map
      Finsupp.equivFunOnFinite.symm.toEmbedding)).filter
      (fun a => ∑ i : Fin m, w i * (a.1 i : ℝ) ≤ T)).card : ℝ) ≤
        (OAI.PiExponent.realWeightedSimplex w T).card := by sorry
