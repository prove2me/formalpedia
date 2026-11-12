-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRecovery_atOption_none_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atOption_none_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:09:19.209201+00:00
-- url     : https://prove2.me/theorems/11874523-8396-4aeb-83b4-a95020619476
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atOption_none_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atOption_none` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/RecoveryOptionMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/RecoveryOptionMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma atOption_none_s238r (d : ℕ) : atOption d (pairBits (pack δ D F S Δ s0 m extra raw,
--       BinarySamplingState.optionBits (n:=n) none))=BinaryFinSet.encode S
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.pack` and `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.optionBits` (definitions bundle `Q238L031` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atOption` (definitions bundle `Q238L040` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.run_source_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/RecoveryOptionMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atOption_none)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L031
import Definitions.Def_Q238L040

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] run
variable {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
  (s0 s : RationalSampling.State n) (m : ℕ) (extra raw : List Bool)
lemma atOption_none_s238r (d : ℕ) : atOption d (pairBits (pack δ D F S Δ s0 m extra raw,
    BinarySamplingState.optionBits (n:=n) none))=BinaryFinSet.encode S := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end
