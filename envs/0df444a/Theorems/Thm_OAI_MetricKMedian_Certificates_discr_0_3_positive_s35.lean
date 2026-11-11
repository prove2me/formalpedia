-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Certificates_discr_0_3_positive_s35
-- name    : OAI.MetricKMedian.Certificates.discr_0_3_positive_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:12:16.672943+00:00
-- url     : https://prove2.me/theorems/4ae34e9e-7054-499a-859c-e62515ef1724
-- title:
--   OAI.MetricKMedian.Certificates.discr_0_3_positive_s35: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Certificates.discr_0_3_positive` of [lean/OAI/Combinatorics/KMedian/Analysis/BernsteinFalse.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/BernsteinFalse.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Certificates`):
--
--   ```lean
--   theorem discr_0_3_positive_s35 {X : ℝ} (ha : (3 / 200) ≤ X) (hb : X ≤ 1) :
--       (1 / 1000000) ≤ discr false 3 X
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Certificates.discr` (definitions bundle `OAIQ035K002` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Certificates.bernCoeff_0_3_nonneg_s35` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/BernsteinFalse.lean (declaration OAI.MetricKMedian.Certificates.discr_0_3_positive)

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

theorem discr_0_3_positive_s35 {X : ℝ} (ha : (3 / 200) ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ discr false 3 X := by
  sorry

end MetricKMedian.Certificates
end
end

end OAI
end
