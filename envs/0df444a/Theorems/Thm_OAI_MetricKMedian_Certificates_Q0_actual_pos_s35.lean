-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Certificates_Q0_actual_pos_s35
-- name    : OAI.MetricKMedian.Certificates.Q0_actual_pos_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:40:22.056586+00:00
-- url     : https://prove2.me/theorems/29089820-8451-4249-8115-6ba57324fd0e
-- title:
--   OAI.MetricKMedian.Certificates.Q0_actual_pos_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Certificates`, with `open Analytic`):
--
--   ```lean
--   theorem Q0_actual_pos_s35 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (s : Bool) :
--       0 < ScalarTransfer.Q0 (P x) (A x) (k (1-x))
--         (if s then ScalarTransfer.uZero s else min (1-x) (ScalarTransfer.uZero s)) s
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.A` and `OAI.MetricKMedian.Analytic.P` (definitions bundle `OAIQ035K000` of this split); `OAI.MetricKMedian.Certificates.k` (definitions bundle `OAIQ035K002` of this split); `OAI.MetricKMedian.ScalarTransfer.uZero` (definitions bundle `OAIQ035K011` of this split); `OAI.MetricKMedian.ScalarTransfer.Q0` (definitions bundle `OAIQ035K044` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K044

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

theorem Q0_actual_pos_s35 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (s : Bool) :
    0 < ScalarTransfer.Q0 (P x) (A x) (k (1-x))
      (if s then ScalarTransfer.uZero s else min (1-x) (ScalarTransfer.uZero s)) s := by
  sorry

end MetricKMedian.Certificates

end
end

end OAI
end
