-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_weighted_occupancy_dichotomy_collision
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy_collision
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T09:55:46.885523+00:00
-- url     : https://prove2.me/theorems/cbb4d5ea-60b7-46b7-baee-a81f8cafcb65
-- title:
--   Occupancy mass forces collision mass
-- statement:
--   For any finite subset of at most N groups, occupancy mass at least eta times the number of indices forces the total squared occupancy over all groups to be at least eta squared times the squared number of indices divided by N.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy_collision
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (low : Finset κ)
    {eta N : ℝ}
    (heta : 0 ≤ eta) (hN : 0 < N)
    (hcapacity : (low.card : ℝ) ≤ N)
    (hlowMass :
      eta * (Fintype.card ι : ℝ) ≤
        ∑ a ∈ low,
          (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ)) :
    eta ^ 2 * (Fintype.card ι : ℝ) ^ 2 / N ≤
      ∑ a : κ, (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) ^ 2 := by sorry
