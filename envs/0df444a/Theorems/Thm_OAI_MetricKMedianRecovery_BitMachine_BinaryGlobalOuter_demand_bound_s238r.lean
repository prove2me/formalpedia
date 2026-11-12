-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryGlobalOuter_demand_bound_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.demand_bound_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:19:38.678018+00:00
-- url     : https://prove2.me/theorems/75425519-d1b0-4374-b5a0-40e1b7ed73d2
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.demand_bound_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.demand_bound` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalOuter.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalOuter.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter`, with `open WordOperations WordList LocalSearch Completion`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma demand_bound_s238r (Q : Polynomial ℕ) (I : RationalMetricInput) (M : ℚ) (hM : M∈BinaryInputParser.Metric.flat I) :
--       (BinaryGlobalCall.A.budget Q).eval (BinaryGlobalCall.integralPack I M []).length≤(budget Q).eval I.bits.length
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.flat` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.integralPack` (definitions bundle `Q238L035` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.A.budget` (definitions bundle `Q238L052` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.budget` (definitions bundle `Q238L054` of this split); `OAI.MetricKMedianRecovery.RationalMetricInput` and `OAI.MetricKMedianRecovery.RationalMetricInput.bits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.finite_program_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalOuter.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.demand_bound)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L054

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open WordOperations WordList LocalSearch Completion
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryGlobalCall.run BinaryGlobalCall.demand budget select BinarySanitizedBest.output
lemma demand_bound_s238r (Q : Polynomial ℕ) (I : RationalMetricInput) (M : ℚ) (hM : M∈BinaryInputParser.Metric.flat I) :
    (BinaryGlobalCall.A.budget Q).eval (BinaryGlobalCall.integralPack I M []).length≤(budget Q).eval I.bits.length := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end
