-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySamplingState_remove_pair_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.remove_pair_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:51:42.164282+00:00
-- url     : https://prove2.me/theorems/68c774c2-8ce3-447d-bf94-bd6d2522e2a9
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.remove_pair_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.remove_pair` of [lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingStateMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingStateMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState`, with `open WordOperations WordList BinaryArithmetic RationalSampling`, `open BinaryOpeningPayment (field field_encode)`):
--
--   ```lean
--   lemma remove_pair_s238 (s : RationalSampling.State n) (v : Fin n) : remove (pairBits (encode s,v.val.bits))=encode (s.remove v)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.encode` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.RationalSampling.State.remove` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.remove` (definitions bundle `Q238K031` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.remove_pair_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingStateMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.remove_pair)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K031

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingState
open WordOperations WordList BinaryArithmetic RationalSampling
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
lemma remove_pair_s238 (s : RationalSampling.State n) (v : Fin n) : remove (pairBits (encode s,v.val.bits))=encode (s.remove v) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinarySamplingState

end OAI
end
