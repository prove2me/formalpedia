-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_RefinedRecovery_metric_length_bound_s35
-- name    : OAI.MetricKMedianRecovery.RefinedRecovery.metric_length_bound_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:15:40.33019+00:00
-- url     : https://prove2.me/theorems/a128d900-8baf-4efd-9022-371430c70d01
-- title:
--   OAI.MetricKMedianRecovery.RefinedRecovery.metric_length_bound_s35: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.RefinedRecovery.metric_length_bound` of [lean/OAI/Combinatorics/KMedianRecovery/Refined/Work.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Refined/Work.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.RefinedRecovery`):
--
--   ```lean
--   lemma metric_length_bound_s35 (I : Input) (b : Polynomial ℕ) (h : I.Bounded b) :
--       I.metric.bits.length ≤ (metricLengthPolynomial b).eval I.size
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RefinedRecovery.metricLengthPolynomial` (definitions bundle `Q224R000` of this split); `OAI.MetricKMedianRecovery.RationalMetricInput.bits`, `OAI.MetricKMedianRecovery.RefinedRecovery.Input`, `OAI.MetricKMedianRecovery.RefinedRecovery.Input.Bounded` and `OAI.MetricKMedianRecovery.RefinedRecovery.Input.size` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery_conditional_s35` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Refined/Work.lean (declaration OAI.MetricKMedianRecovery.RefinedRecovery.metric_length_bound)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q224R000

section

attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RefinedRecovery

lemma metric_length_bound_s35 (I : Input) (b : Polynomial ℕ) (h : I.Bounded b) :
    I.metric.bits.length ≤ (metricLengthPolynomial b).eval I.size := by
  sorry

end MetricKMedianRecovery.RefinedRecovery

end OAI
end
