-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_volume_lower_bound
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_simplex_volume_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T02:41:00.590004+00:00
-- url     : https://prove2.me/theorems/4f06ab8a-7c22-471c-8b7e-1f2d9d6a8037
-- title:
--   Lower volume bound for weighted simplex lattice counts
-- statement:
--   For positive weights and a nonnegative cutoff, the weighted simplex volume at that cutoff is at most the number of admissible nonnegative integer vectors.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.DeterminantContradiction.weighted_simplex_volume_lower_bound
    (m : ℕ) (w : Fin m → ℝ) (T : ℝ)
    (hw : ∀ i, 0 < w i) (hT : 0 ≤ T) :
    T ^ m / ((Nat.factorial m : ℝ) * ∏ i : Fin m, w i) ≤
        ((OAI.PiExponent.realWeightedSimplex w T).card : ℝ) := by sorry
