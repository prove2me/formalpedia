-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySamplingOracle_weight_pair_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.weight_pair_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:53:19.375413+00:00
-- url     : https://prove2.me/theorems/a018e8ed-6a3b-43a0-af72-c9038c27bd1d
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.weight_pair_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.weight_pair` of [lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingStateMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingStateMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma weight_pair_s238r (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (w : Fin n) :
--       weight (pairBits (pack δ D S Δ s,w.val.bits))=RationalSampling.clientWeight δ S Δ s w
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.RationalSampling.clientWeight` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.pack` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.weight` (definitions bundle `Q238L029` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.weight_pair_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.total_pack_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingStateMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.weight_pair)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L029

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
lemma weight_pair_s238r (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (w : Fin n) :
    weight (pairBits (pack δ D S Δ s,w.val.bits))=RationalSampling.clientWeight δ S Δ s w := by
  sorry
end MetricKMedianRecovery.BitMachine.BinarySamplingOracle

end OAI
end
