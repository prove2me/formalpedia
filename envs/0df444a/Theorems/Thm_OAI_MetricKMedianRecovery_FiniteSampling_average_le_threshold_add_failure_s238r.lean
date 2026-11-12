-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_FiniteSampling_average_le_threshold_add_failure_s238r
-- name    : OAI.MetricKMedianRecovery.FiniteSampling.average_le_threshold_add_failure_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:24:26.729187+00:00
-- url     : https://prove2.me/theorems/afbd4f1c-fcdf-4d9d-9e43-94c8342ef10d
-- title:
--   OAI.MetricKMedianRecovery.FiniteSampling.average_le_threshold_add_failure_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.FiniteSampling.average_le_threshold_add_failure` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/BestFallback.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/BestFallback.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.FiniteSampling`):
--
--   ```lean
--   lemma average_le_threshold_add_failure_s238r (X : Ω → ℝ) {B M : ℝ}
--       (hB : 0 ≤ B) (hX : ∀ s, X s ≤ M) :
--       average X ≤ B + probability (fun s => B < X s)*M
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.FiniteSampling.average` and `OAI.MetricKMedianRecovery.FiniteSampling.probability` (definitions bundle `Q238L002` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.finite_program_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.designated_recovery_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.amplified_s238r` and `OAI.MetricKMedianRecovery.global_application` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/BestFallback.lean (declaration OAI.MetricKMedianRecovery.FiniteSampling.average_le_threshold_add_failure)

import Mathlib
import Definitions.Def_Q238L002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
variable {Ω Y : Type*} [Fintype Ω] [Nonempty Ω]

lemma average_le_threshold_add_failure_s238r (X : Ω → ℝ) {B M : ℝ}
    (hB : 0 ≤ B) (hX : ∀ s, X s ≤ M) :
    average X ≤ B + probability (fun s => B < X s)*M := by
  sorry

end MetricKMedianRecovery.FiniteSampling

end OAI
end
