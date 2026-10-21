-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_general_asymptotic
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_simplex_general_asymptotic
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T23:19:46.038803+00:00
-- url     : https://prove2.me/theorems/2ad53fd7-ad8b-4714-b5fc-3f6c3c3f0b23
-- title:
--   General scaled weighted simplex lattice-count asymptotic
-- statement:
--   For any finite family of positive weights and positive scale, the number of nonnegative integer vectors in the weighted simplex at cutoff A times H, divided by H to the dimension, tends to A to the dimension divided by the factorial of the dimension times the product of the weights.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.DeterminantContradiction.weighted_simplex_general_asymptotic
    (m : ℕ) (w : Fin m → ℝ) (A : ℝ)
    (hw : ∀ i, 0 < w i) (hA : 0 < A) :
    Tendsto
      (fun H : ℝ => ((OAI.PiExponent.realWeightedSimplex w (A * H)).card : ℝ) / H ^ m)
      atTop
      (𝓝 (A ^ m /
        ((Nat.factorial m : ℝ) * ∏ i : Fin m, w i))) := by sorry
