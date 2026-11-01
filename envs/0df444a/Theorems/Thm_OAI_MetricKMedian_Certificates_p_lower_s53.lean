-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Certificates_p_lower_s53
-- name    : OAI.MetricKMedian.Certificates.p_lower_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:29:12.641886+00:00
-- url     : https://prove2.me/theorems/267a92bc-161b-4f84-8c7f-b0cb3e2bbcaa
-- title:
--   OAI.MetricKMedian.Certificates.p_lower_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Certificates.p_lower` of [lean/OAI/Combinatorics/KMedian/Analysis/PolynomialBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/PolynomialBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Certificates`):
--
--   ```lean
--   theorem p_lower_s53 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
--       (1651507 / 6250000) ≤ p X
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Certificates.p` (definitions bundle `OAIQ053K002` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedian.Certificates.Q1_actual_pos_s53`, `OAI.MetricKMedian.Certificates.T1_actual_pos_s53`, `OAI.MetricKMedian.Certificates.T2_actual_pos_s53` and `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s53` of this split import it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/PolynomialBounds.lean (declaration OAI.MetricKMedian.Certificates.p_lower)

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

theorem p_lower_s53 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1651507 / 6250000) ≤ p X := by
  sorry

end MetricKMedian.Certificates
end
end

end OAI
end
