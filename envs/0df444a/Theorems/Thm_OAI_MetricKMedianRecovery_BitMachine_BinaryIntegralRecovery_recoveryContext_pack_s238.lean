-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_recoveryContext_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:54:51.079835+00:00
-- url     : https://prove2.me/theorems/23111f24-f174-48ef-99d5-ea5c5c18ef3a
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery`, with `open WordOperations WordList Sampling.Comparison`, `open BinaryOpeningPayment (field field_encode)`):
--
--   ```lean
--   lemma recoveryContext_pack_s238 (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
--       recoveryContext (pack δ D F S Δ P m g seed complete)=
--         BinaryRecovery.pack δ D F S Δ RationalSampling.State.initial m g complete
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Rounding.cap` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` and `OAI.MetricKMedianRecovery.RationalSampling.State.initial` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.pack` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.pack` (definitions bundle `Q238K031` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext` (definitions bundle `Q238K034` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.run_source_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext_pack)

import Mathlib
import Definitions.Def_Q238K031
import Definitions.Def_Q238K034

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open WordOperations WordList Sampling.Comparison
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] params cfg mword precision sampleRaw completeRaw extra src
  BinarySampler.Parameters.run BinarySampler.Parameters.precision BinarySampler.Parameters.unary
variable {n b : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
  (g : List Bool) (seed : Fin (2*m)→Fin b→Bool) (complete : List Bool)
lemma recoveryContext_pack_s238 (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    recoveryContext (pack δ D F S Δ P m g seed complete)=
      BinaryRecovery.pack δ D F S Δ RationalSampling.State.initial m g complete := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

end OAI
end
