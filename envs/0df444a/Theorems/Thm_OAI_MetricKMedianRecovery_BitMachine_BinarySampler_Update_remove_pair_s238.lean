-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Update_remove_pair_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.remove_pair_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:56:54.083443+00:00
-- url     : https://prove2.me/theorems/56328e7a-c3f4-4ea8-b945-7e341d3e0b0f
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.remove_pair_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.remove_pair` of [lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerUpdate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerUpdate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field field_computes field_encode)`, `open Weights (actionField )`):
--
--   ```lean
--   lemma remove_pair_s238 (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) (w : D)
--       (h : RationalSampling.chosenId δ S Δ s w<n) :
--       remove (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
--         RationalSampling.actionCode D M E J (Sum.inr (Sum.inl w))))=
--         BinarySamplingState.optionBits (RationalSampling.retain m (s.remove ⟨RationalSampling.chosenId δ S Δ s w,h⟩))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` and `OAI.MetricKMedianRecovery.RationalSampling.chosenId` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Sampling.Entry` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.RationalSampling.retain` and `OAI.MetricKMedianRecovery.RationalSampling.State.remove` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.RationalSampling.actionCode`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.config` and `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.optionBits` (definitions bundle `Q238K022` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.remove` (definitions bundle `Q238K035` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run_pair_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerUpdate.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.remove_pair)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K035

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Update
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Weights (actionField )
variable {n : ℕ}
lemma remove_pair_s238 (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) (w : D)
    (h : RationalSampling.chosenId δ S Δ s w<n) :
    remove (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
      RationalSampling.actionCode D M E J (Sum.inr (Sum.inl w))))=
      BinarySamplingState.optionBits (RationalSampling.retain m (s.remove ⟨RationalSampling.chosenId δ S Δ s w,h⟩)) := by
  sorry

end MetricKMedianRecovery.BitMachine.BinarySampler.Update

end OAI
end
