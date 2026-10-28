-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Certificates_h_upper_s35
-- name    : OAI.MetricKMedian.Certificates.h_upper_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:33:20.969355+00:00
-- url     : https://prove2.me/theorems/b1f95707-02c3-46ab-b881-e3a675f9dae8
-- title:
--   OAI.MetricKMedian.Certificates.h_upper_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Certificates`):
--
--   ```lean
--   theorem h_upper_s35 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
--       0 ≤ 197/500-h X
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Certificates.h` (definitions bundle `OAIQ035K002` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

theorem h_upper_s35 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 197/500-h X := by
  sorry

end MetricKMedian.Certificates
end
end

end OAI
end
