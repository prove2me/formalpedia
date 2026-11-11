-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Update_radius_pair_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.radius_pair_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:02:34.172666+00:00
-- url     : https://prove2.me/theorems/93c72c0f-a919-4c77-92dc-b4c5d3d20f22
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.radius_pair_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.radius_pair` of [lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerUpdateParts.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerUpdateParts.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field field_computes field_encode)`, `open Weights (actionField )`):
--
--   ```lean
--   lemma radius_pair_s238 (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n)
--       (w : D) (e : Sampling.Entry M E J) :
--       radius (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
--         RationalSampling.actionCode D M E J (Sum.inr (Sum.inr (w,e)))))=
--         BinaryMenu.optBits (RationalSampling.menuRadius δ D P κ m M E J s w e)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Sampling.Entry` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.RationalSampling.menuRadius` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.optBits` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.RationalSampling.actionCode`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.config` and `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.optionBits` (definitions bundle `Q238K022` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.radius` (definitions bundle `Q238K038` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.ball_pair_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run_pair_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerUpdateParts.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.radius_pair)

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
open Weights (actionField )
attribute [local irreducible] BinaryMenu.radius WordList.filterWith Client.row
variable {n : ℕ}
lemma radius_pair_s238 (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n)
    (w : D) (e : Sampling.Entry M E J) :
    radius (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
      RationalSampling.actionCode D M E J (Sum.inr (Sum.inr (w,e)))))=
      BinaryMenu.optBits (RationalSampling.menuRadius δ D P κ m M E J s w e) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinarySampler.Update

end OAI
end
