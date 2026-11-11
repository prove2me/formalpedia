-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Fair_demandWord_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.demandWord_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:54:05.763302+00:00
-- url     : https://prove2.me/theorems/6cf4c03e-d664-4156-b930-f2fe6a75a592
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.demandWord_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.demandWord_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryDemand.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryDemand.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair`, with `open WordOperations Polynomial`, `open BinaryOpeningPayment (field field_computes )`):
--
--   ```lean
--   lemma demandWord_pack_s238 : (demandWord (pack δ D F S Δ P m g bits)).length=count D Δ m
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Rounding.cap` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.pack` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.count` (definitions bundle `Q238K026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.demandWord` (definitions bundle `Q238K034` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape.demandWord_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Repeat_FiniteTape_run_of_repeat_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.run_source_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryDemand.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.demandWord_pack)

import Mathlib
import Definitions.Def_Q238K034

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open WordOperations Polynomial
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] extra raw RawTake.run
variable {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (g bits : List Bool) (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16))
include hm hΔ in
lemma demandWord_pack_s238 : (demandWord (pack δ D F S Δ P m g bits)).length=count D Δ m := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair

end OAI
end
