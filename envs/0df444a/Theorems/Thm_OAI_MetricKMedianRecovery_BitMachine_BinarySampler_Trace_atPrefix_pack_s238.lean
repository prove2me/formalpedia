-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Trace_atPrefix_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.atPrefix_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:08:47.364049+00:00
-- url     : https://prove2.me/theorems/2b5b2fba-50b9-448a-8dc7-488e611d56fc
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.atPrefix_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.atPrefix_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerTraceMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerTraceMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace`, with `open WordOperations WordList`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma atPrefix_pack_s238 {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b : ℕ)
--       (seeds : List (Fin b→Bool)) (j : ℕ) :
--       atPrefix (pairBits (Loop.runPack (config δ D F S Δ P κ m M E J) m b seeds,j.bits))=
--         BinarySamplingState.optionBits ((seeds.take j).foldl (RationalSampling.next δ D F S Δ P κ m M E J b)
--           (some RationalSampling.State.initial))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.RationalSampling.State.initial` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.runPack` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.RationalSampling.next` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.config` and `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.optionBits` (definitions bundle `Q238K022` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.atPrefix` (definitions bundle `Q238K040` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.run_pack_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerTraceMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.atPrefix_pack)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K040

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Trace
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinarySeed.rows Take.run Loop.run BinaryEllipsoidInitial.indices WordList.mapWith
lemma atPrefix_pack_s238 {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b : ℕ)
    (seeds : List (Fin b→Bool)) (j : ℕ) :
    atPrefix (pairBits (Loop.runPack (config δ D F S Δ P κ m M E J) m b seeds,j.bits))=
      BinarySamplingState.optionBits ((seeds.take j).foldl (RationalSampling.next δ D F S Δ P κ m M E J b)
        (some RationalSampling.State.initial)) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinarySampler.Trace

end OAI
end
