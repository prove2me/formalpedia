-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_volume_bounds
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_simplex_volume_bounds
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T02:36:05.620194+00:00
-- url     : https://prove2.me/theorems/ba571e94-364e-402c-a4ef-f8148b3e5b66
-- title:
--   Finite volume bounds for weighted simplex lattice counts
-- statement:
--   For positive weights and any nonnegative cutoff, the weighted simplex lattice count lies between the real simplex volumes at that cutoff and at the cutoff increased by the sum of the weights. This includes dimension zero and cutoff zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.DeterminantContradiction.weighted_simplex_volume_bounds
    (m : ℕ) (w : Fin m → ℝ) (T : ℝ)
    (hw : ∀ i, 0 < w i) (hT : 0 ≤ T) :
    T ^ m / ((Nat.factorial m : ℝ) * ∏ i : Fin m, w i) ≤
        ((OAI.PiExponent.realWeightedSimplex w T).card : ℝ) ∧
      ((OAI.PiExponent.realWeightedSimplex w T).card : ℝ) ≤
        (T + ∑ i : Fin m, w i) ^ m /
          ((Nat.factorial m : ℝ) * ∏ i : Fin m, w i) := by sorry
