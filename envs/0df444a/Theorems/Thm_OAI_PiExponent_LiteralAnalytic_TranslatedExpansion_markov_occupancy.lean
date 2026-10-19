-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_markov_occupancy
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.markov_occupancy
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T03:06:29.567523+00:00
-- url     : https://prove2.me/theorems/649d0604-e8e0-4940-ba77-2d7eb6107d25
-- title:
--   Finite Markov occupancy bound
-- statement:
--   For a finite index type with nonnegative weights, if the total weight is strictly below the number of indices times a nonnegative threshold times (1 − eta), then at least eta times the number of indices have weight at most the threshold. This generic estimate removes the group-fiber bookkeeping from the parent. A proof counts indices above the threshold, lower-bounds the total by their contribution, and rearranges; threshold zero and the empty type are included.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.markov_occupancy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) {t eta : ℝ}
    (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hf : ∀ i, 0 ≤ f i)
    (hsum : (∑ i : ι, f i) < (Fintype.card ι : ℝ) * t * (1 - eta)) :
    eta * (Fintype.card ι : ℝ) ≤
      ((Finset.univ : Finset ι).filter (fun i => f i ≤ t)).card := by sorry
