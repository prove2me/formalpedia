-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_FiniteSampling_probability_prefix_s238
-- name    : OAI.MetricKMedianRecovery.FiniteSampling.probability_prefix_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:15:46.596096+00:00
-- url     : https://prove2.me/theorems/24664b58-798d-4c71-bdee-1553a5cd5e26
-- title:
--   OAI.MetricKMedianRecovery.FiniteSampling.probability_prefix_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.FiniteSampling.probability_prefix` of [lean/OAI/Combinatorics/KMedianRecovery/Sampling/FairPrefix.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/FairPrefix.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.FiniteSampling`):
--
--   ```lean
--   lemma probability_prefix_s238 {n N : ℕ} (h : n≤N) (E : (Fin n→Bool)→Prop) :
--       probability (fun seed:Fin N→Bool=>E (fun i=>seed (Fin.castLE h i)))=probability E
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.FiniteSampling.probability` (definitions bundle `Q238K002` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.finite_program_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.designated_recovery_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.polynomial_recovery_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryRecovery_positiveSeed_probability_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.result_success_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/FairPrefix.lean (declaration OAI.MetricKMedianRecovery.FiniteSampling.probability_prefix)

import Mathlib
import Definitions.Def_Q238K002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
lemma probability_prefix_s238 {n N : ℕ} (h : n≤N) (E : (Fin n→Bool)→Prop) :
    probability (fun seed:Fin N→Bool=>E (fun i=>seed (Fin.castLE h i)))=probability E := by
  sorry
end MetricKMedianRecovery.FiniteSampling

end OAI
end
