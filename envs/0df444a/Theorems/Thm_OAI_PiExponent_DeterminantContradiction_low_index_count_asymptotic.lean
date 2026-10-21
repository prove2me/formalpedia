-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_low_index_count_asymptotic
-- name    : OAI.PiExponent.DeterminantContradiction.low_index_count_asymptotic
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T23:08:15.13883+00:00
-- url     : https://prove2.me/theorems/b4625ce3-3416-4b6c-a55b-1e64d1273f5b
-- title:
--   Asymptotic volume of the closed low-index simplex
-- statement:
--   For admissible fixed data, the low-index count divided by H^m converges to the volume coefficient of its closed weighted simplex with cutoff A H.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.DeterminantContradiction.low_index_count_asymptotic
    {nu : ℝ} (d : FixedData nu) :
    Tendsto
      (fun H : ℝ => (lowIndexCount d H : ℝ) / H ^ d.m)
      atTop
      (𝓝 (((d.base.A : ℝ) ^ d.m) /
        ((Nat.factorial d.m : ℝ) *
          ∏ i : Fin d.m, d.x (i.val + 1)))) := by sorry
