-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Certificates_Yprime_actual_bounds_s53
-- name    : OAI.MetricKMedian.Certificates.Yprime_actual_bounds_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:22:06.284794+00:00
-- url     : https://prove2.me/theorems/045fe862-23f7-41cd-bdb7-224328f51c11
-- title:
--   OAI.MetricKMedian.Certificates.Yprime_actual_bounds_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Certificates.Yprime_actual_bounds` of [lean/OAI/Combinatorics/KMedian/Analysis/ComparisonCertificates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/ComparisonCertificates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Certificates`, with `open Analytic`):
--
--   ```lean
--   theorem Yprime_actual_bounds_s53 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
--       (hside : 1-x ≤ 1/2) :
--       h (1-x) ≤ ScalarTransfer.Yprime (P x) (k (1-x)) x+(13/25)*k (1-x) ∧
--         1/4 ≤ ScalarTransfer.Yprime (P x) (k (1-x)) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.P` (definitions bundle `OAIQ053K000` of this split); `OAI.MetricKMedian.Certificates.h` and `OAI.MetricKMedian.Certificates.k` (definitions bundle `OAIQ053K002` of this split); `OAI.MetricKMedian.ScalarTransfer.Yprime` (definitions bundle `OAIQ053K011` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/ComparisonCertificates.lean (declaration OAI.MetricKMedian.Certificates.Yprime_actual_bounds)

import Mathlib
import Definitions.Def_OAIQ053K000
import Definitions.Def_OAIQ053K002
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

theorem Yprime_actual_bounds_s53 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hside : 1-x ≤ 1/2) :
    h (1-x) ≤ ScalarTransfer.Yprime (P x) (k (1-x)) x+(13/25)*k (1-x) ∧
      1/4 ≤ ScalarTransfer.Yprime (P x) (k (1-x)) x := by
  sorry

end MetricKMedian.Certificates

end
end

end OAI
end
