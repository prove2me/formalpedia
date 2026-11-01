-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Certificates_Q0_actual_pos_s53
-- name    : OAI.MetricKMedian.Certificates.Q0_actual_pos_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:32:32.351995+00:00
-- url     : https://prove2.me/theorems/56d4f32b-28d5-4af5-bd15-c045cc2b9e23
-- title:
--   OAI.MetricKMedian.Certificates.Q0_actual_pos_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Certificates.Q0_actual_pos` of [lean/OAI/Combinatorics/KMedian/Analysis/ComparisonCertificates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/ComparisonCertificates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Certificates`, with `open Analytic`):
--
--   ```lean
--   theorem Q0_actual_pos_s53 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (s : Bool) :
--       0 < ScalarTransfer.Q0 (P x) (A x) (k (1-x))
--         (if s then ScalarTransfer.uZero s else min (1-x) (ScalarTransfer.uZero s)) s
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.A` and `OAI.MetricKMedian.Analytic.P` (definitions bundle `OAIQ053K000` of this split); `OAI.MetricKMedian.Certificates.k` (definitions bundle `OAIQ053K002` of this split); `OAI.MetricKMedian.ScalarTransfer.uZero` (definitions bundle `OAIQ053K011` of this split); `OAI.MetricKMedian.ScalarTransfer.Q0` (definitions bundle `OAIQ053K027` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/ComparisonCertificates.lean (declaration OAI.MetricKMedian.Certificates.Q0_actual_pos)

import Mathlib
import Definitions.Def_OAIQ053K000
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
namespace MetricKMedian.Certificates

open Analytic

theorem Q0_actual_pos_s53 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (s : Bool) :
    0 < ScalarTransfer.Q0 (P x) (A x) (k (1-x))
      (if s then ScalarTransfer.uZero s else min (1-x) (ScalarTransfer.uZero s)) s := by
  sorry

end MetricKMedian.Certificates

end
end

end OAI
end
