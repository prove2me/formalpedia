-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryNormalizeInput_P_clients_bits_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.clients_bits_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:58:10.331453+00:00
-- url     : https://prove2.me/theorems/d310f259-8945-4d89-9427-b183e8bda961
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.clients_bits_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.clients_bits` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/NormalizeInput.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/NormalizeInput.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P`, with `open WordOperations WordList`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma clients_bits_s238r (I : RationalMetricInput) : clients I.bits=BinaryFinSet.encode I.clients
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.clients` (definitions bundle `Q238L035` of this split); `OAI.MetricKMedianRecovery.RationalMetricInput` and `OAI.MetricKMedianRecovery.RationalMetricInput.bits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.demand_bound_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.select_bits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zero_bits_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.prep_bits_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/NormalizeInput.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.clients_bits)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L035

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
lemma clients_bits_s238r (I : RationalMetricInput) : clients I.bits=BinaryFinSet.encode I.clients := by
  sorry
end P
attribute [local irreducible] P.points P.clients P.facilities
  BinaryInputParser.Metric.count BinaryInputParser.Metric.budget
  BinaryNormalization.run BinaryNormalization.cap BinaryNormalization.mesh
end MetricKMedianRecovery.BitMachine.BinaryNormalizeInput

end OAI
end
