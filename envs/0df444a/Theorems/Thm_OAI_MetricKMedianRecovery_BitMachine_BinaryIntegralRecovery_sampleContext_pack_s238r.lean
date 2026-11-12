-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_sampleContext_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.sampleContext_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:03:38.390011+00:00
-- url     : https://prove2.me/theorems/1b142908-d46f-45f2-8d8a-83e86f6f5ec5
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.sampleContext_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.sampleContext_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery`, with `open WordOperations WordList Sampling.Comparison`, `open BinaryOpeningPayment (field field_encode)`):
--
--   ```lean
--   lemma sampleContext_pack_s238r (seed : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool)
--       (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
--       sampleContext (pack δ D F S Δ P m g seed complete)=
--         BinarySampler.Trace.pack (BinarySampler.config δ D F S Δ P (1/1000000) m BinarySampler.Parameters.M
--           BinarySampler.Parameters.E (RadiusMenus.thirdSize mainKappa m)) m seed
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RadiusMenus.thirdSize`, `OAI.MetricKMedianRecovery.Rounding.cap`, `OAI.MetricKMedianRecovery.Sampling.Comparison.integralPrecision`, `OAI.MetricKMedianRecovery.Sampling.Comparison.mainKappa`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Parameters.E` and `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Parameters.M` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.pack` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.pack` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.config` (definitions bundle `Q238L031` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.sampleContext` (definitions bundle `Q238L037` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.run_source_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.sampleContext_pack)

import Mathlib
import Definitions.Def_Q238L031
import Definitions.Def_Q238L037

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
lemma sampleContext_pack_s238r (seed : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool)
    (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    sampleContext (pack δ D F S Δ P m g seed complete)=
      BinarySampler.Trace.pack (BinarySampler.config δ D F S Δ P (1/1000000) m BinarySampler.Parameters.M
        BinarySampler.Parameters.E (RadiusMenus.thirdSize mainKappa m)) m seed := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

end OAI
end
