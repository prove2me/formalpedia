-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Sampling_Comparison_covered_completion_sum_s238
-- name    : OAI.MetricKMedianRecovery.Sampling.Comparison.covered_completion_sum_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:33:29.606991+00:00
-- url     : https://prove2.me/theorems/b546e06f-03f2-4607-a721-45cf8a1e78b1
-- title:
--   OAI.MetricKMedianRecovery.Sampling.Comparison.covered_completion_sum_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Sampling.Comparison.covered_completion_sum` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/SingleRadiusRatio.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/SingleRadiusRatio.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Sampling.Comparison`):
--
--   ```lean
--   lemma covered_completion_sum_s238 (C : Comparison D S O) (hD : D.Nonempty)
--       (kappa theta : ℝ) (hk : 0 ≤ kappa) (ht : 0 ≤ theta)
--       (s : State V) (hs : C.Correct hD kappa s)
--       (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
--       (∑ o ∈ C.covered s, ∑ p ∈ cluster D C.assign o,
--         (dist p o + theta*(dist (C.leaderPair s o).1 o+(C.leaderPair s o).2))) ≤
--         (1+theta*(2+kappa)*(6/5:ℝ))*(∑ o ∈ C.covered s, clusterCost D C.assign o)+
--           theta*kappa*(26/5:ℝ)*comparisonCost D C.assign
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Sampling.State` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison`, `OAI.MetricKMedianRecovery.Sampling.cluster`, `OAI.MetricKMedianRecovery.Sampling.clusterCost` and `OAI.MetricKMedianRecovery.Sampling.comparisonCost` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.bad` (definitions bundle `Q238K015` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.covered` and `OAI.MetricKMedianRecovery.Sampling.Comparison.leaderPair` (definitions bundle `Q238K016` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.Correct` (definitions bundle `Q238K022` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.Sampling.Comparison.successful_completion_charge_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/SingleRadiusRatio.lean (declaration OAI.MetricKMedianRecovery.Sampling.Comparison.covered_completion_sum)

import Mathlib
import Definitions.Def_Q238K022

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

lemma covered_completion_sum_s238 (C : Comparison D S O) (hD : D.Nonempty)
    (kappa theta : ℝ) (hk : 0 ≤ kappa) (ht : 0 ≤ theta)
    (s : State V) (hs : C.Correct hD kappa s)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
    (∑ o ∈ C.covered s, ∑ p ∈ cluster D C.assign o,
      (dist p o + theta*(dist (C.leaderPair s o).1 o+(C.leaderPair s o).2))) ≤
      (1+theta*(2+kappa)*(6/5:ℝ))*(∑ o ∈ C.covered s, clusterCost D C.assign o)+
        theta*kappa*(26/5:ℝ)*comparisonCost D C.assign := by
  sorry

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end
