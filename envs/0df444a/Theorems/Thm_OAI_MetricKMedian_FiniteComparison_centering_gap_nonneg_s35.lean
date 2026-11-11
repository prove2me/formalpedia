-- Prove2me | Theorems.Thm_OAI_MetricKMedian_FiniteComparison_centering_gap_nonneg_s35
-- name    : OAI.MetricKMedian.FiniteComparison.centering_gap_nonneg_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:13:35.280533+00:00
-- url     : https://prove2.me/theorems/17c4a61a-db58-45aa-9cc7-43899c5ab9b5
-- title:
--   OAI.MetricKMedian.FiniteComparison.centering_gap_nonneg_s35: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.FiniteComparison.centering_gap_nonneg` of [lean/OAI/Combinatorics/KMedian/Analysis/FiniteAverages.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/FiniteAverages.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.FiniteComparison`):
--
--   ```lean
--   theorem centering_gap_nonneg_s35 {p q : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2)
--       (hq : q ≤ 1) (s : Bool) : 0 ≤ k p s - (C p s * psi p q - (1 - q))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteComparison.C` (definitions bundle `OAIQ035K002` of this split); `OAI.MetricKMedian.FiniteComparison.psi` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.FiniteComparison.k` (definitions bundle `OAIQ035K015` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s35` and `OAI.MetricKMedian.FiniteComparison.finite_charge_s35` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/FiniteAverages.lean (declaration OAI.MetricKMedian.FiniteComparison.centering_gap_nonneg)

import Mathlib
import Definitions.Def_OAIQ035K015

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.FiniteComparison

theorem centering_gap_nonneg_s35 {p q : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hq : q ≤ 1) (s : Bool) : 0 ≤ k p s - (C p s * psi p q - (1 - q)) := by
  sorry

end MetricKMedian.FiniteComparison

end
end

end OAI
end
