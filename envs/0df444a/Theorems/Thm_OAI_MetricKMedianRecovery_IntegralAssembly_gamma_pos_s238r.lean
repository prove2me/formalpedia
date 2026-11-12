-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_IntegralAssembly_gamma_pos_s238r
-- name    : OAI.MetricKMedianRecovery.IntegralAssembly.gamma_pos_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:29:28.699257+00:00
-- url     : https://prove2.me/theorems/3b9e92a3-4c11-4a33-83b0-4fda246b2191
-- title:
--   OAI.MetricKMedianRecovery.IntegralAssembly.gamma_pos_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.IntegralAssembly.gamma_pos` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/LowCandidate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/LowCandidate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.IntegralAssembly`, with `open LocalSearch Anchoring Completion Sampling FiniteSampling`):
--
--   ```lean
--   lemma gamma_pos_s238r : 0 < gamma
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` (definitions bundle `Q238L009` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.finite_program_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalRounding.rounded_program_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.finite_program_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.uniform_program_long_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.demandWord_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.repack_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.integral_recovery_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.ranges_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.polynomial_program_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.sampleContext_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.integral_spec_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce_s238r` and `OAI.MetricKMedianRecovery.global_application` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/LowCandidate.lean (declaration OAI.MetricKMedianRecovery.IntegralAssembly.gamma_pos)

import Mathlib
import Definitions.Def_Q238L009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralAssembly
open LocalSearch Anchoring Completion Sampling FiniteSampling

lemma gamma_pos_s238r : 0 < gamma := by
  sorry

end MetricKMedianRecovery.IntegralAssembly

end OAI
end
