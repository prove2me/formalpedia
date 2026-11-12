-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralAll_cost_le_surplus_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.cost_le_surplus_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:22:56.149264+00:00
-- url     : https://prove2.me/theorems/3b0cae77-d493-4205-8996-423fdde61c57
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.cost_le_surplus_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.cost_le_surplus` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralAll.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralAll.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll`, with `open Completion Sampling.Comparison`):
--
--   ```lean
--   lemma cost_le_surplus_s238r (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→ Fin n→ℚ)
--       (hδ : ∀ i j,(δ i j:ℝ)=dist i j) (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
--       (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤ k) (L : ℕ) (hL : L≤ F.card)
--       (U : Finset (Fin n)) (hUF : U⊆F) (hU : U.Nonempty) (hUk : U.card≤ k)
--       (hu : BinaryMetricSurplus.run v C (BinaryMetricSurplus.pack δ D F Δ (k-L) L)=BinaryFinSet.encode U) :
--       realCost D (output v C Q d δ D F S Δ k g raw)≤ realCost D U
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Completion.realCost` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.pack` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.run` (definitions bundle `Q238L052` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.output` (definitions bundle `Q238L054` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.finite_program_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralAll.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.cost_le_surplus)

import Mathlib
import Definitions.Def_Q238L054

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open Completion Sampling.Comparison
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
attribute [local irreducible] output words surplus BinaryIntegralDispatch.output BinaryIntegralDispatch.run
lemma cost_le_surplus_s238r (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→ Fin n→ℚ)
    (hδ : ∀ i j,(δ i j:ℝ)=dist i j) (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤ k) (L : ℕ) (hL : L≤ F.card)
    (U : Finset (Fin n)) (hUF : U⊆F) (hU : U.Nonempty) (hUk : U.card≤ k)
    (hu : BinaryMetricSurplus.run v C (BinaryMetricSurplus.pack δ D F Δ (k-L) L)=BinaryFinSet.encode U) :
    realCost D (output v C Q d δ D F S Δ k g raw)≤ realCost D U := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

end OAI
end
