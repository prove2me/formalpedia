-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Certificates_bernCoeff_1_3_nonneg_s35
-- name    : OAI.MetricKMedian.Certificates.bernCoeff_1_3_nonneg_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:11:25.777196+00:00
-- url     : https://prove2.me/theorems/9c1d4f07-84ca-402a-aa32-da5b13054805
-- title:
--   OAI.MetricKMedian.Certificates.bernCoeff_1_3_nonneg_s35: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Certificates.bernCoeff_1_3_nonneg` of [lean/OAI/Combinatorics/KMedian/Analysis/QuadraticEnvelopes.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/QuadraticEnvelopes.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Certificates`):
--
--   ```lean
--   theorem bernCoeff_1_3_nonneg_s35 {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
--       (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff true 3 X r
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Certificates.bernCoeff` (definitions bundle `OAIQ035K002` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Certificates.polynomial_charge_margin_s35` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/QuadraticEnvelopes.lean (declaration OAI.MetricKMedian.Certificates.bernCoeff_1_3_nonneg)

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

theorem bernCoeff_1_3_nonneg_s35 {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff true 3 X r := by
  sorry

end MetricKMedian.Certificates

end
end

end OAI
end
