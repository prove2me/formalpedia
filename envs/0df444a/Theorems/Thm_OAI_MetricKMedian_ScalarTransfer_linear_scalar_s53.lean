-- Prove2me | Theorems.Thm_OAI_MetricKMedian_ScalarTransfer_linear_scalar_s53
-- name    : OAI.MetricKMedian.ScalarTransfer.linear_scalar_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:36:21.513927+00:00
-- url     : https://prove2.me/theorems/a27b3e7f-2294-4696-ad26-541bff94247b
-- title:
--   OAI.MetricKMedian.ScalarTransfer.linear_scalar_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.ScalarTransfer.linear_scalar` of [lean/OAI/Combinatorics/KMedian/Analysis/NormalizedTransfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/NormalizedTransfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.ScalarTransfer`):
--
--   ```lean
--   theorem linear_scalar_s53 {p a k x w r : ℝ} (hp0 : 0 ≤ p) (hw : w ≤ 1-x)
--       (hr0 : 0 ≤ r) (hr : r ≤ 1) (s : Bool)
--       (hQ0 : 0 ≤ Q0 p a k (if s then uZero s else min (1-x) (uZero s)) s)
--       (hQ1 : 0 ≤ Q1 p a k x s) :
--       d s*(stdM p a w r s-stdL p a x w r s) ≤ stdK p k x w r s
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.ScalarTransfer.d` and `OAI.MetricKMedian.ScalarTransfer.uZero` (definitions bundle `OAIQ053K011` of this split); `OAI.MetricKMedian.ScalarTransfer.Q0`, `OAI.MetricKMedian.ScalarTransfer.Q1`, `OAI.MetricKMedian.ScalarTransfer.stdK`, `OAI.MetricKMedian.ScalarTransfer.stdL` and `OAI.MetricKMedian.ScalarTransfer.stdM` (definitions bundle `OAIQ053K027` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/NormalizedTransfer.lean (declaration OAI.MetricKMedian.ScalarTransfer.linear_scalar)

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

theorem linear_scalar_s53 {p a k x w r : ℝ} (hp0 : 0 ≤ p) (hw : w ≤ 1-x)
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
