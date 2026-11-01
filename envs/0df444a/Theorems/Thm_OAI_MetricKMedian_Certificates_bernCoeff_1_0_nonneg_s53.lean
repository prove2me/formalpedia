-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Certificates_bernCoeff_1_0_nonneg_s53
-- name    : OAI.MetricKMedian.Certificates.bernCoeff_1_0_nonneg_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:25:48.839719+00:00
-- url     : https://prove2.me/theorems/3e869a24-2e78-45b0-99bb-81090950c7b4
-- title:
--   OAI.MetricKMedian.Certificates.bernCoeff_1_0_nonneg_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Certificates.bernCoeff_1_0_nonneg` of [lean/OAI/Combinatorics/KMedian/Analysis/QuadraticEnvelopes.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/QuadraticEnvelopes.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Certificates`):
--
--   ```lean
--   theorem bernCoeff_1_0_nonneg_s53 {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
--       (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff true 0 X r
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Certificates.bernCoeff` (definitions bundle `OAIQ053K002` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Certificates.polynomial_charge_margin_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/QuadraticEnvelopes.lean (declaration OAI.MetricKMedian.Certificates.bernCoeff_1_0_nonneg)

import Mathlib
import Definitions.Def_OAIQ053K002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

theorem bernCoeff_1_0_nonneg_s53 {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff true 0 X r := by
  sorry

end MetricKMedian.Certificates

end
end

end OAI
end
