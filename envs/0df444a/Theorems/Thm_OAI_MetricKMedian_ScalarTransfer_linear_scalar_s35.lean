-- Prove2me | Theorems.Thm_OAI_MetricKMedian_ScalarTransfer_linear_scalar_s35
-- name    : OAI.MetricKMedian.ScalarTransfer.linear_scalar_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:14:11.855095+00:00
-- url     : https://prove2.me/theorems/2b8c2ebe-9117-40ea-8d3c-42d17f19265a
-- title:
--   OAI.MetricKMedian.ScalarTransfer.linear_scalar_s35: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.ScalarTransfer.linear_scalar` of [lean/OAI/Combinatorics/KMedian/Analysis/NormalizedTransfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/NormalizedTransfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.ScalarTransfer`):
--
--   ```lean
--   theorem linear_scalar_s35 {p a k x w r : ℝ} (hp0 : 0 ≤ p) (hw : w ≤ 1-x)
--       (hr0 : 0 ≤ r) (hr : r ≤ 1) (s : Bool)
--       (hQ0 : 0 ≤ Q0 p a k (if s then uZero s else min (1-x) (uZero s)) s)
--       (hQ1 : 0 ≤ Q1 p a k x s) :
--       d s*(stdM p a w r s-stdL p a x w r s) ≤ stdK p k x w r s
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.ScalarTransfer.d` and `OAI.MetricKMedian.ScalarTransfer.uZero` (definitions bundle `OAIQ035K011` of this split); `OAI.MetricKMedian.ScalarTransfer.stdL` and `OAI.MetricKMedian.ScalarTransfer.stdM` (definitions bundle `OAIQ035K036` of this split); `OAI.MetricKMedian.ScalarTransfer.Q0` and `OAI.MetricKMedian.ScalarTransfer.Q1` (definitions bundle `OAIQ035K044` of this split); `OAI.MetricKMedian.ScalarTransfer.stdK` (definitions bundle `OAIQ035K045` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s35` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/NormalizedTransfer.lean (declaration OAI.MetricKMedian.ScalarTransfer.linear_scalar)

import Mathlib
import Definitions.Def_OAIQ035K044
import Definitions.Def_OAIQ035K045

section

attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

theorem linear_scalar_s35 {p a k x w r : ℝ} (hp0 : 0 ≤ p) (hw : w ≤ 1-x)
    (hr0 : 0 ≤ r) (hr : r ≤ 1) (s : Bool)
    (hQ0 : 0 ≤ Q0 p a k (if s then uZero s else min (1-x) (uZero s)) s)
    (hQ1 : 0 ≤ Q1 p a k x s) :
    d s*(stdM p a w r s-stdL p a x w r s) ≤ stdK p k x w r s := by
  sorry

end MetricKMedian.ScalarTransfer

end
end

end OAI
end
