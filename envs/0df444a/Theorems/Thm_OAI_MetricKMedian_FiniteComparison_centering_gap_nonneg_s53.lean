-- Prove2me | Theorems.Thm_OAI_MetricKMedian_FiniteComparison_centering_gap_nonneg_s53
-- name    : OAI.MetricKMedian.FiniteComparison.centering_gap_nonneg_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:31:47.223338+00:00
-- url     : https://prove2.me/theorems/0afd6981-762c-43a5-b82c-758af70058d6
-- title:
--   OAI.MetricKMedian.FiniteComparison.centering_gap_nonneg_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.FiniteComparison.centering_gap_nonneg` of [lean/OAI/Combinatorics/KMedian/Analysis/FiniteAverages.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/FiniteAverages.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.FiniteComparison`):
--
--   ```lean
--   theorem centering_gap_nonneg_s53 {p q : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2)
--       (hq : q ≤ 1) (s : Bool) : 0 ≤ k p s - (C p s * psi p q - (1 - q))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteComparison.C`, `OAI.MetricKMedian.FiniteComparison.k` and `OAI.MetricKMedian.FiniteComparison.psi` (definitions bundle `OAIQ053K006` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s53` and `OAI.MetricKMedian.FiniteComparison.finite_comparison_s53` of this split import it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/FiniteAverages.lean (declaration OAI.MetricKMedian.FiniteComparison.centering_gap_nonneg)

import Mathlib
import Definitions.Def_OAIQ053K006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.FiniteComparison

theorem centering_gap_nonneg_s53 {p q : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hq : q ≤ 1) (s : Bool) : 0 ≤ k p s - (C p s * psi p q - (1 - q)) := by
  sorry

end MetricKMedian.FiniteComparison

end
end

end OAI
end
