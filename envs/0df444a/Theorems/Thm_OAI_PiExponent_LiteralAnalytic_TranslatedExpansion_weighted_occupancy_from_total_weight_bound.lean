-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_weighted_occupancy_from_total_weight_bound
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_from_total_weight_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T13:17:44.141503+00:00
-- url     : https://prove2.me/theorems/22aa7ac3-9f7d-4cdf-8e57-692601087d27
-- title:
--   Occupancy bound from a strict total-weight bound
-- statement:
--   If all group weights are nonnegative and their total across indices is strictly less than the number of indices times H·A·(1−eta), then the indices in groups whose weights are at most A·H have total occupancy at least eta times the number of indices.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_from_total_weight_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ)
    {H A eta : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta)
    (hweight : ∀ a, 0 ≤ weight a)
    (hsum :
      (∑ i : ι, weight (group i)) <
        (Fintype.card ι : ℝ) * H * (A * (1 - eta))) :
    eta * (Fintype.card ι : ℝ) ≤
      ∑ a ∈ ((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)),
        (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) := by sorry
