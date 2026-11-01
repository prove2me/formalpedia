-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Certificates_T1_actual_pos_s53
-- name    : OAI.MetricKMedian.Certificates.T1_actual_pos_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:21:40.794325+00:00
-- url     : https://prove2.me/theorems/57887009-9c64-42d2-a23b-7c2a24965dac
-- title:
--   OAI.MetricKMedian.Certificates.T1_actual_pos_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Certificates.T1_actual_pos` of [lean/OAI/Combinatorics/KMedian/Analysis/ComparisonCertificates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/ComparisonCertificates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Certificates`, with `open Analytic`):
--
--   ```lean
--   theorem T1_actual_pos_s53 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) :
--       0 < ScalarTransfer.T1 (P x) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.P` (definitions bundle `OAIQ053K000` of this split); `OAI.MetricKMedian.ScalarTransfer.T1` (definitions bundle `OAIQ053K011` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/ComparisonCertificates.lean (declaration OAI.MetricKMedian.Certificates.T1_actual_pos)

import Mathlib
import Definitions.Def_OAIQ053K000
import Definitions.Def_OAIQ053K011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

open Analytic

theorem T1_actual_pos_s53 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    0 < ScalarTransfer.T1 (P x) x := by
  sorry

end MetricKMedian.Certificates

end
end

end OAI
end
