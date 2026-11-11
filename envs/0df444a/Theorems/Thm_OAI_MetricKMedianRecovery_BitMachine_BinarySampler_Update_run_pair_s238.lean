-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Update_run_pair_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run_pair_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:03:21.405554+00:00
-- url     : https://prove2.me/theorems/4e5c4c7a-a130-4f3b-97ab-7ed237f03d7f
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run_pair_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run_pair` of [lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerUpdate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerUpdate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma run_pair_s238 (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ)
--       (s : Option (RationalSampling.State n)) (a : Sampling.Action D M E J) :
--       run (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits s),RationalSampling.actionCode D M E J a))=
--         BinarySamplingState.optionBits (RationalSampling.update δ D F S Δ P κ m M E J s a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Sampling.Action` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.RationalSampling.update` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.RationalSampling.actionCode`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.config` and `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.optionBits` (definitions bundle `Q238K022` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run` (definitions bundle `Q238K038` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proofs of `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Loop_step_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.atPrefix_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerUpdate.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run_pair)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K038

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Update
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
lemma run_pair_s238 (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ)
    (s : Option (RationalSampling.State n)) (a : Sampling.Action D M E J) :
    run (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits s),RationalSampling.actionCode D M E J a))=
      BinarySamplingState.optionBits (RationalSampling.update δ D F S Δ P κ m M E J s a) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinarySampler.Update

end OAI
end
