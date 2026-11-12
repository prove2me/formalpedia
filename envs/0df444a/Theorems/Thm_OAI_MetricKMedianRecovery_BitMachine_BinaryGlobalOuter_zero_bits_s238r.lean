-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryGlobalOuter_zero_bits_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zero_bits_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:02:56.874886+00:00
-- url     : https://prove2.me/theorems/567b00b8-e6be-4e31-8ff9-1c6533419459
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zero_bits_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zero_bits` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalOuter.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalOuter.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter`, with `open WordOperations WordList LocalSearch Completion`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma zero_bits_s238r (I : RationalMetricInput) : zero I.bits=BinaryFinSet.encode
--       (BinaryGlobalZero.output I.distance I.clients I.facilities I.facilities_nonempty)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.output` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zero` (definitions bundle `Q238L038` of this split); `OAI.MetricKMedianRecovery.RationalMetricInput` and `OAI.MetricKMedianRecovery.RationalMetricInput.bits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.finite_program_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalOuter.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zero_bits)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L038

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open WordOperations WordList LocalSearch Completion
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinarySanitizedBest.output
lemma zero_bits_s238r (I : RationalMetricInput) : zero I.bits=BinaryFinSet.encode
    (BinaryGlobalZero.output I.distance I.clients I.facilities I.facilities_nonempty) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end
