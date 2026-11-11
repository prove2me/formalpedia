-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryNormalizeInput_P_facilities_bits_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.facilities_bits_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:56:33.387189+00:00
-- url     : https://prove2.me/theorems/d474d378-3d24-48a1-8f00-b8628ebb7d90
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.facilities_bits_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.facilities_bits` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/NormalizeInput.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/NormalizeInput.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P`, with `open WordOperations WordList`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma facilities_bits_s238 (I : RationalMetricInput) : facilities I.bits=BinaryFinSet.encode I.facilities
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.facilities` (definitions bundle `Q238K035` of this split); `OAI.MetricKMedianRecovery.RationalMetricInput` and `OAI.MetricKMedianRecovery.RationalMetricInput.bits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.fallback_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.select_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zero_bits_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.facilities_bits_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/NormalizeInput.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.facilities_bits)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K035

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNormalizeInput
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
namespace P
lemma facilities_bits_s238 (I : RationalMetricInput) : facilities I.bits=BinaryFinSet.encode I.facilities := by
  sorry
end P
attribute [local irreducible] P.points P.clients P.facilities
  BinaryInputParser.Metric.count BinaryInputParser.Metric.budget
  BinaryNormalization.run BinaryNormalization.cap BinaryNormalization.mesh
end MetricKMedianRecovery.BitMachine.BinaryNormalizeInput

end OAI
end
