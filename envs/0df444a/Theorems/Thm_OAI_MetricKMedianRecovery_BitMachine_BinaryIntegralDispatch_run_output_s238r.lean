-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralDispatch_run_output_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.run_output_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:18:45.023349+00:00
-- url     : https://prove2.me/theorems/69ae84f0-0eb3-4d2f-b17b-1a4bf414a32e
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.run_output_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.run_output` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralDispatchLaws.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralDispatchLaws.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch`, with `open WordOperations WordList Completion Sampling.Comparison FiniteSampling`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma run_output_s238r (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
--       (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
--       (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F k)=BinaryFinSet.encode S) :
--       run Q d (pack δ D F Δ k g raw)=BinaryFinSet.encode (output Q d δ D F S Δ k g raw)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.pack` (definitions bundle `Q238L029` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.pack` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.run` (definitions bundle `Q238L037` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.run` (definitions bundle `Q238L050` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.output` (definitions bundle `Q238L053` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.lift_probability_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.designated_recovery_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralDispatchLaws.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.run_output)

import Mathlib
import Definitions.Def_Q238L053

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch
open WordOperations WordList Completion Sampling.Comparison FiniteSampling
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] anchor BinaryMetricAnchor.run BinaryIntegralRecovery.Guesses.run recoveryParams demand
variable {n : ℕ}
lemma run_output_s238r (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F k)=BinaryFinSet.encode S) :
    run Q d (pack δ D F Δ k g raw)=BinaryFinSet.encode (output Q d δ D F S Δ k g raw) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

end OAI
end
