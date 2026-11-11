-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Certificates_v_upper_s35
-- name    : OAI.MetricKMedian.Certificates.v_upper_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:13:32.93031+00:00
-- url     : https://prove2.me/theorems/efc72d2f-2045-4120-a218-bcd4bbe17c8f
-- title:
--   OAI.MetricKMedian.Certificates.v_upper_s35: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Certificates.v_upper` of [lean/OAI/Combinatorics/KMedian/Analysis/PolynomialBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/PolynomialBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Certificates`):
--
--   ```lean
--   theorem v_upper_s35 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
--       0 ≤ 217/125 - v X
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Certificates.v` (definitions bundle `OAIQ035K002` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s35` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/PolynomialBounds.lean (declaration OAI.MetricKMedian.Certificates.v_upper)

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

theorem v_upper_s35 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 217/125 - v X := by
  sorry

end MetricKMedian.Certificates
end
end

end OAI
end
