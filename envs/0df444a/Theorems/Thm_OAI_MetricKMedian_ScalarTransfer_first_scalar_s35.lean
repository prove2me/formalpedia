-- Prove2me | Theorems.Thm_OAI_MetricKMedian_ScalarTransfer_first_scalar_s35
-- name    : OAI.MetricKMedian.ScalarTransfer.first_scalar_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:13:50.547102+00:00
-- url     : https://prove2.me/theorems/e259b954-b428-4dd5-b358-4efecad6fe90
-- title:
--   OAI.MetricKMedian.ScalarTransfer.first_scalar_s35: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.ScalarTransfer.first_scalar` of [lean/OAI/Combinatorics/KMedian/Analysis/NormalizedTransfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/NormalizedTransfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.ScalarTransfer`):
--
--   ```lean
--   theorem first_scalar_s35 {p x w m r : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
--       (hx0 : 0 ≤ x) (hx : x ≤ 1) (hw0 : 0 ≤ w) (hw : w ≤ 1-x)
--       (hr0 : 0 < r) (hr : r ≤ 1)
--       (hm : (1+x)*(m+2*x*p) = 2*x*(1-p))
--       (hT1 : 0 ≤ T1 p x) (hT2 : 0 ≤ T2 p x) (s : Bool) :
--       m+(2-bit s)*p*(x+w)-(2/5)*(p*w^2)/r ≤ c p s*(1-p)/(1-p*r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.ScalarTransfer.bit` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.ScalarTransfer.T1` and `OAI.MetricKMedian.ScalarTransfer.T2` (definitions bundle `OAIQ035K011` of this split); `OAI.MetricKMedian.ScalarTransfer.c` (definitions bundle `OAIQ035K024` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s35` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/NormalizedTransfer.lean (declaration OAI.MetricKMedian.ScalarTransfer.first_scalar)

import Mathlib
import Definitions.Def_OAIQ035K024

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

theorem first_scalar_s35 {p x w m r : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hw0 : 0 ≤ w) (hw : w ≤ 1-x)
    (hr0 : 0 < r) (hr : r ≤ 1)
    (hm : (1+x)*(m+2*x*p) = 2*x*(1-p))
    (hT1 : 0 ≤ T1 p x) (hT2 : 0 ≤ T2 p x) (s : Bool) :
    m+(2-bit s)*p*(x+w)-(2/5)*(p*w^2)/r ≤ c p s*(1-p)/(1-p*r) := by
  sorry

end MetricKMedian.ScalarTransfer

end
end

end OAI
end
