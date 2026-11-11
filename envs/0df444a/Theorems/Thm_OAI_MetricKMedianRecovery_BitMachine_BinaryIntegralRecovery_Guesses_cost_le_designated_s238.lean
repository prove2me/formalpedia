-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Guesses_cost_le_designated_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.cost_le_designated_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:08:24.316663+00:00
-- url     : https://prove2.me/theorems/a700e04f-1b87-4fa9-b88b-1a005bcd6567
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.cost_le_designated_s238 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.cost_le_designated` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoverySelection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoverySelection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses`, with `open Completion Sampling Sampling.Comparison FiniteSampling`):
--
--   ```lean
--   lemma cost_le_designated_s238 (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
--       (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℕ) (g raw : List Bool)
--       (p m : ℕ) (hp : p≤D.card*Δ) (hm : m≤n) (U : Finset (Fin n))
--       (hUF : U⊆F) (hU : U.Nonempty) (hUk : U.card≤S.card)
--       (hrun : Repeat.FiniteTape.run Q d (Fair.pack δ D F S Δ p m g raw)=BinaryFinSet.encode U) :
--       realCost D (output Q d δ D F S Δ g raw) ≤ realCost D U
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Completion.realCost` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.pack` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.output` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape.run` (definitions bundle `Q238K040` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.polynomial_recovery_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoverySelection.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.cost_le_designated)

import Mathlib
import Definitions.Def_Q238K040

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open Completion Sampling Sampling.Comparison FiniteSampling
variable {n : ℕ}
variable [PseudoMetricSpace (Fin n)]
lemma cost_le_designated_s238 (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℕ) (g raw : List Bool)
    (p m : ℕ) (hp : p≤D.card*Δ) (hm : m≤n) (U : Finset (Fin n))
    (hUF : U⊆F) (hU : U.Nonempty) (hUk : U.card≤S.card)
    (hrun : Repeat.FiniteTape.run Q d (Fair.pack δ D F S Δ p m g raw)=BinaryFinSet.encode U) :
    realCost D (output Q d δ D F S Δ g raw) ≤ realCost D U := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

end OAI
end
