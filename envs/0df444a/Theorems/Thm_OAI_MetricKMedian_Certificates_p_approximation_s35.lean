-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Certificates_p_approximation_s35
-- name    : OAI.MetricKMedian.Certificates.p_approximation_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:33:47.407988+00:00
-- url     : https://prove2.me/theorems/391a4d77-36be-474f-999e-bbaaba16df6c
-- title:
--   OAI.MetricKMedian.Certificates.p_approximation_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Certificates`, with `open Analytic`):
--
--   ```lean
--   theorem p_approximation_s35 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
--       |p (1 - x) - P x| ≤ 3 / 400000
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.P` (definitions bundle `OAIQ035K000` of this split); `OAI.MetricKMedian.Certificates.p` (definitions bundle `OAIQ035K002` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedian.Certificates.Q0_actual_pos_s35`, `OAI.MetricKMedian.Certificates.Q1_actual_pos_s35`, `OAI.MetricKMedian.Certificates.T1_actual_pos_s35`, `OAI.MetricKMedian.Certificates.T2_actual_pos_s35`, `OAI.MetricKMedian.Certificates.Y_actual_bounds_s35`, `OAI.MetricKMedian.Certificates.Yprime_actual_bounds_s35`, `OAI.MetricKMedian.Certificates.k_envelope_s35` and `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s35` of this split import it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K000
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

open Analytic

theorem p_approximation_s35 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |p (1 - x) - P x| ≤ 3 / 400000 := by
  sorry

end MetricKMedian.Certificates

end
end

end OAI
end
