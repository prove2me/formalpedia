-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Certificates_Y_actual_bounds_s53
-- name    : OAI.MetricKMedian.Certificates.Y_actual_bounds_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:32:52.494899+00:00
-- url     : https://prove2.me/theorems/83e5ddb7-9353-42fa-9280-9d511c8e06cc
-- title:
--   OAI.MetricKMedian.Certificates.Y_actual_bounds_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Certificates.Y_actual_bounds` of [lean/OAI/Combinatorics/KMedian/Analysis/ComparisonCertificates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/ComparisonCertificates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Certificates`, with `open Analytic`):
--
--   ```lean
--   theorem Y_actual_bounds_s53 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (s : Bool)
--       (hside : s = true ∨ 1-x ≥ 1/2) :
--       h (1-x) ≤ ScalarTransfer.Y (P x) (k (1-x)) x s ∧
--         1/4 ≤ ScalarTransfer.Y (P x) (k (1-x)) x s
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.P` (definitions bundle `OAIQ053K000` of this split); `OAI.MetricKMedian.Certificates.h` and `OAI.MetricKMedian.Certificates.k` (definitions bundle `OAIQ053K002` of this split); `OAI.MetricKMedian.ScalarTransfer.Y` (definitions bundle `OAIQ053K027` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/ComparisonCertificates.lean (declaration OAI.MetricKMedian.Certificates.Y_actual_bounds)

import Mathlib
import Definitions.Def_OAIQ053K000
import Definitions.Def_OAIQ053K027

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

theorem Y_actual_bounds_s53 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (s : Bool)
    (hside : s = true ∨ 1-x ≥ 1/2) :
    h (1-x) ≤ ScalarTransfer.Y (P x) (k (1-x)) x s ∧
      1/4 ≤ ScalarTransfer.Y (P x) (k (1-x)) x s := by
  sorry

end MetricKMedian.Certificates

end
end

end OAI
end
