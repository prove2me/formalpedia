-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySamplingOracle_weight_pair_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.weight_pair_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:52:02.348816+00:00
-- url     : https://prove2.me/theorems/ddc8a01a-a855-4bd9-a48e-4ae18b111cc0
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.weight_pair_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.weight_pair` of [lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingStateMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingStateMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma weight_pair_s238 (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (w : Fin n) :
--       weight (pairBits (pack δ D S Δ s,w.val.bits))=RationalSampling.clientWeight δ S Δ s w
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.pack` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.RationalSampling.clientWeight` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.weight` (definitions bundle `Q238K030` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.weight_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.total_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinarySamplingOracle_weights_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingStateMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.weight_pair)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K030

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingOracle
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
lemma weight_pair_s238 (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (w : Fin n) :
    weight (pairBits (pack δ D S Δ s,w.val.bits))=RationalSampling.clientWeight δ S Δ s w := by
  sorry
end MetricKMedianRecovery.BitMachine.BinarySamplingOracle

end OAI
end
