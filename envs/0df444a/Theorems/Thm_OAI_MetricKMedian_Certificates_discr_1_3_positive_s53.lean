-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Certificates_discr_1_3_positive_s53
-- name    : OAI.MetricKMedian.Certificates.discr_1_3_positive_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:27:40.908994+00:00
-- url     : https://prove2.me/theorems/76b74844-e744-4c9f-a567-2d11cf84e18c
-- title:
--   OAI.MetricKMedian.Certificates.discr_1_3_positive_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Certificates.discr_1_3_positive` of [lean/OAI/Combinatorics/KMedian/Analysis/BernsteinTrue.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/BernsteinTrue.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Certificates`):
--
--   ```lean
--   theorem discr_1_3_positive_s53 {X : ℝ} (ha : (1 / 10) ≤ X) (hb : X ≤ (3 / 4)) :
--       (1 / 1000000) ≤ discr true 3 X
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Certificates.discr` (definitions bundle `OAIQ053K002` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Certificates.bernCoeff_1_3_nonneg_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/BernsteinTrue.lean (declaration OAI.MetricKMedian.Certificates.discr_1_3_positive)

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

theorem discr_1_3_positive_s53 {X : ℝ} (ha : (1 / 10) ≤ X) (hb : X ≤ (3 / 4)) :
    (1 / 1000000) ≤ discr true 3 X := by
  sorry

end MetricKMedian.Certificates

end
end

end OAI
end
