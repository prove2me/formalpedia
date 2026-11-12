-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_LocalSearch_optimum_attained_exact_s238r
-- name    : OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_exact_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:29:41.778983+00:00
-- url     : https://prove2.me/theorems/23f046d3-7e5f-4b34-9f61-313c12137631
-- title:
--   OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_exact_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_exact` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/Produce.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Produce.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.LocalSearch`):
--
--   ```lean
--   lemma optimum_attained_exact_s238r (F D : Finset V) (hF : F.Nonempty) (r : ℕ)
--       (hr : 0 < r) (hrF : r ≤ F.card) :
--       ∃ O ⊆ F, O.Nonempty ∧ O.card = r ∧ cost D O = optimum F D r
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.LocalSearch.cost` and `OAI.MetricKMedianRecovery.LocalSearch.optimum` (definitions bundle `Q238L010` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.finite_program_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.low_candidate_s238r` and `OAI.MetricKMedianRecovery.Sensitivity.sensitive_optimum_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Produce.lean (declaration OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_exact)

import Mathlib
import Definitions.Def_Q238L010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

lemma optimum_attained_exact_s238r (F D : Finset V) (hF : F.Nonempty) (r : ℕ)
    (hr : 0 < r) (hrF : r ≤ F.card) :
    ∃ O ⊆ F, O.Nonempty ∧ O.card = r ∧ cost D O = optimum F D r := by
  sorry

end MetricKMedianRecovery.LocalSearch

end OAI
end
