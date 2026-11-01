-- Prove2me | Theorems.Thm_OAI_MetricKMedian_ScalarTransfer_first_scalar_s53
-- name    : OAI.MetricKMedian.ScalarTransfer.first_scalar_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:36:17.009314+00:00
-- url     : https://prove2.me/theorems/e891e7ee-f68f-42f8-a8ab-d73dea09f890
-- title:
--   OAI.MetricKMedian.ScalarTransfer.first_scalar_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.ScalarTransfer.first_scalar` of [lean/OAI/Combinatorics/KMedian/Analysis/NormalizedTransfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/NormalizedTransfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.ScalarTransfer`):
--
--   ```lean
--   theorem first_scalar_s53 {p x w m r : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
--       (hx0 : 0 ≤ x) (hx : x ≤ 1) (hw0 : 0 ≤ w) (hw : w ≤ 1-x)
--       (hr0 : 0 < r) (hr : r ≤ 1)
--       (hm : (1+x)*(m+2*x*p) = 2*x*(1-p))
--       (hT1 : 0 ≤ T1 p x) (hT2 : 0 ≤ T2 p x) (s : Bool) :
--       m+(2-bit s)*p*(x+w)-(2/5)*(p*w^2)/r ≤ c p s*(1-p)/(1-p*r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.ScalarTransfer.bit` (definitions bundle `OAIQ053K006` of this split); `OAI.MetricKMedian.ScalarTransfer.T1` and `OAI.MetricKMedian.ScalarTransfer.T2` (definitions bundle `OAIQ053K011` of this split); `OAI.MetricKMedian.ScalarTransfer.c` (definitions bundle `OAIQ053K027` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/NormalizedTransfer.lean (declaration OAI.MetricKMedian.ScalarTransfer.first_scalar)

import Mathlib
import Definitions.Def_OAIQ053K027

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

theorem first_scalar_s53 {p x w m r : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
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
