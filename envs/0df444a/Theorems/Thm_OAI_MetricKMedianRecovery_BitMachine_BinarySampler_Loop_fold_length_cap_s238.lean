-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Loop_fold_length_cap_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.fold_length_cap_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:29:10.028955+00:00
-- url     : https://prove2.me/theorems/bc34bf79-0541-4ac2-b0f1-efe02206580c
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.fold_length_cap_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.fold_length_cap` of [lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerResources.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerResources.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop`, with `open WordOperations WordList BinaryArithmetic RationalHeight`, `open BinaryOpeningPayment (field field_encode)`):
--
--   ```lean
--   lemma fold_length_cap_s238 (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b : ℕ) (seeds : List (Fin b→Bool)) (j : ℕ) :
--       (BinarySamplingState.optionBits ((seeds.take j).foldl (RationalSampling.next δ D F S Δ P κ m M E J b) (some RationalSampling.State.initial))).length≤
--         capPoly.eval (runPack (config δ D F S Δ P κ m M E J) m b seeds).length
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.capPoly` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.RationalSampling.State.initial` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.runPack` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.RationalSampling.next` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.config` and `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.optionBits` (definitions bundle `Q238K022` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.atPrefix_pack_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerResources.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.fold_length_cap)

import Mathlib
import Definitions.Def_Q238K021
import Definitions.Def_Q238K022

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Loop
open WordOperations WordList BinaryArithmetic RationalHeight
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
lemma fold_length_cap_s238 (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b : ℕ) (seeds : List (Fin b→Bool)) (j : ℕ) :
    (BinarySamplingState.optionBits ((seeds.take j).foldl (RationalSampling.next δ D F S Δ P κ m M E J b) (some RationalSampling.State.initial))).length≤
      capPoly.eval (runPack (config δ D F S Δ P κ m M E J) m b seeds).length := by
  sorry
end MetricKMedianRecovery.BitMachine.BinarySampler.Loop

end OAI
end
