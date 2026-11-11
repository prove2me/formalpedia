-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_LocalSearch_optimum_attained_s238
-- name    : OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:23:01.220863+00:00
-- url     : https://prove2.me/theorems/5105a938-3651-40c4-a139-5da35d2f7505
-- title:
--   OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.LocalSearch.optimum_attained` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/Produce.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Produce.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.LocalSearch`):
--
--   ```lean
--   lemma optimum_attained_s238 (F D : Finset V) (hF : F.Nonempty) (r : ℕ) (hr : 0 < r) :
--       ∃ O ⊆ F, O.Nonempty ∧ O.card ≤ r ∧ cost D O = optimum F D r
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.LocalSearch.cost` and `OAI.MetricKMedianRecovery.LocalSearch.optimum` (definitions bundle `Q238K015` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.finite_program_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.finite_program_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.low_candidate_s238` and `OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_exact_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Produce.lean (declaration OAI.MetricKMedianRecovery.LocalSearch.optimum_attained)

import Mathlib
import Definitions.Def_Q238K015

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

lemma optimum_attained_s238 (F D : Finset V) (hF : F.Nonempty) (r : ℕ) (hr : 0 < r) :
    ∃ O ⊆ F, O.Nonempty ∧ O.card ≤ r ∧ cost D O = optimum F D r := by
  sorry

end MetricKMedianRecovery.LocalSearch

end OAI
end
