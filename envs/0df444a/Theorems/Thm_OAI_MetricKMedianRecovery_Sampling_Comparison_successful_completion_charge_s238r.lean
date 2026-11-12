-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Sampling_Comparison_successful_completion_charge_s238r
-- name    : OAI.MetricKMedianRecovery.Sampling.Comparison.successful_completion_charge_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:32:16.249973+00:00
-- url     : https://prove2.me/theorems/2c4ec0d6-5b90-43ca-96dd-147a6a26af33
-- title:
--   OAI.MetricKMedianRecovery.Sampling.Comparison.successful_completion_charge_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Sampling.Comparison.successful_completion_charge` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/SuccessfulCompletionCharge.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/SuccessfulCompletionCharge.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Sampling.Comparison`):
--
--   ```lean
--   lemma successful_completion_charge_s238r (C : Comparison D S O) (hD : D.Nonempty)
--       (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
--       (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
--       (J : Finset V) (I : ℝ) (hI : I ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
--       (hT : C.nearTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign) :
--       2*I + (∑ o ∈ C.good, ∑ p ∈ cluster D C.assign o, dist p (C.proxy o)) +
--         (∑ o ∈ C.covered s, ∑ p ∈ cluster D C.assign o,
--           (dist p o+(19/50:ℝ)*(dist (C.leaderPair s o).1 o+(C.leaderPair s o).2))) +
--         (∑ o ∈ C.bad \ C.covered s, ∑ p ∈ cluster D C.assign o,
--           if p ∈ J then dist p o else reference S Δ s p) ≤
--         (240258179/125000000:ℝ)*comparisonCost D C.assign
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Sampling.State` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison`, `OAI.MetricKMedianRecovery.Sampling.cluster` and `OAI.MetricKMedianRecovery.Sampling.comparisonCost` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.Sampling.reference`, `OAI.MetricKMedianRecovery.Sampling.Comparison.Correct`, `OAI.MetricKMedianRecovery.Sampling.Comparison.bad`, `OAI.MetricKMedianRecovery.Sampling.Comparison.covered`, `OAI.MetricKMedianRecovery.Sampling.Comparison.leaderPair` and `OAI.MetricKMedianRecovery.Sampling.Comparison.nearTotal` (definitions bundle `Q238L011` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.Sampling.Comparison.surrogate_success_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/SuccessfulCompletionCharge.lean (declaration OAI.MetricKMedianRecovery.Sampling.Comparison.successful_completion_charge)

import Mathlib
import Definitions.Def_Q238L011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

lemma successful_completion_charge_s238r (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (J : Finset V) (I : ℝ) (hI : I ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (hT : C.nearTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign) :
    2*I + (∑ o ∈ C.good, ∑ p ∈ cluster D C.assign o, dist p (C.proxy o)) +
      (∑ o ∈ C.covered s, ∑ p ∈ cluster D C.assign o,
        (dist p o+(19/50:ℝ)*(dist (C.leaderPair s o).1 o+(C.leaderPair s o).2))) +
      (∑ o ∈ C.bad \ C.covered s, ∑ p ∈ cluster D C.assign o,
        if p ∈ J then dist p o else reference S Δ s p) ≤
      (240258179/125000000:ℝ)*comparisonCost D C.assign := by
  sorry

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end
