-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_weighted_occupancy_dichotomy
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T09:41:03.809061+00:00
-- url     : https://prove2.me/theorems/5a70a775-13d8-4ed2-9c54-3f1bb27eeeee
-- title:
--   Weighted occupancy dichotomy
-- statement:
--   Given nonnegative group weights, a bound on the number of low-weight indices, and a lower bound on total weight, either the row occupancies have the stated collision mass or the total weight exceeds its baseline by the stated amount.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ)
    {H A eta N bbar : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta) (hN : 0 < N)
    (hweight : ∀ a, 0 ≤ weight a)
    (hmean : (Fintype.card ι : ℝ) * H * bbar ≤ ∑ i : ι, weight (group i))
    (hcapacity : (((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)).card : ℝ) ≤ N) :
    (eta ^ 2 * (Fintype.card ι : ℝ) ^ 2 / N ≤
      ∑ a : κ, (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) ^ 2) ∨
    ( (Fintype.card ι : ℝ) * H * (A * (1 - eta) - bbar) ≤
      (∑ i : ι, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar) := by sorry
