-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralDispatch_cost_le_call_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.cost_le_call_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:15:58.394199+00:00
-- url     : https://prove2.me/theorems/f062e3ea-154b-450f-9c21-3a6a1c5093d4
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.cost_le_call_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.cost_le_call` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralDispatchLaws.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralDispatchLaws.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch`, with `open WordOperations WordList Completion Sampling.Comparison FiniteSampling`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma cost_le_call_s238 (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
--       (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
--       (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k) (r : ℕ) (hr : r≤F.card)
--       (U : Finset (Fin n)) (hUF : U⊆F) (hU : U.Nonempty) (hUk : U.card≤k)
--       (hu : call Q d (pairBits (pack δ D F Δ k g raw,r.bits))=BinaryFinSet.encode U) :
--       realCost D (output Q d δ D F S Δ k g raw) ≤ realCost D U
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Completion.realCost` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.pack` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.call` (definitions bundle `Q238K049` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.output` (definitions bundle `Q238K052` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.designated_recovery_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralDispatchLaws.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.cost_le_call)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K052

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
variable [PseudoMetricSpace (Fin n)]
lemma cost_le_call_s238 (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k) (r : ℕ) (hr : r≤F.card)
    (U : Finset (Fin n)) (hUF : U⊆F) (hU : U.Nonempty) (hUk : U.card≤k)
    (hu : call Q d (pairBits (pack δ D F Δ k g raw,r.bits))=BinaryFinSet.encode U) :
    realCost D (output Q d δ D F S Δ k g raw) ≤ realCost D U := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

end OAI
end
