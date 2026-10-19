-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_weighted_occupancy_dichotomy_low_mass
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy_low_mass
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T09:55:34.739411+00:00
-- url     : https://prove2.me/theorems/aa0af2c6-eace-4f4b-b38d-ad339bc81ecf
-- title:
--   Low-weight occupancy from a failed surplus bound
-- statement:
--   If the surplus alternative fails, the total occupancy of groups whose weights are at most A times H is at least eta times the number of indices.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy_low_mass
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ)
    {H A eta bbar : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta)
    (hweight : ∀ a, 0 ≤ weight a)
    (hsurplus :
      ¬ ((Fintype.card ι : ℝ) * H * (A * (1 - eta) - bbar) ≤
        (∑ i : ι, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar)) :
    eta * (Fintype.card ι : ℝ) ≤
      ∑ a ∈ ((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)),
        (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) := by sorry
