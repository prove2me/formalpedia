-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralDispatch_demand_bound_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.demand_bound_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:16:24.344361+00:00
-- url     : https://prove2.me/theorems/844bbc37-7567-45c4-87cb-628e8dce67cc
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.demand_bound_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.demand_bound` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralDispatchLaws.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralDispatchLaws.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch`, with `open WordOperations WordList Completion Sampling.Comparison FiniteSampling`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma demand_bound_s238r (Q : Polynomial ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ k : ℕ)
--       (g : List Bool) (r : ℕ) (hr : r≤F.card)
--       (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F r)=BinaryFinSet.encode S) :
--       (R.budget Q).eval (R.pack δ D F S Δ g []).length≤(budget Q).eval (pack δ D F Δ k g []).length
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.pack` (definitions bundle `Q238L029` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.pack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.R.pack` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.run` (definitions bundle `Q238L037` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.R.budget` (definitions bundle `Q238L045` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.budget` (definitions bundle `Q238L052` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.designated_recovery_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralDispatchLaws.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.demand_bound)

import Mathlib
import Definitions.Def_Q238L052

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch
open WordOperations WordList Completion Sampling.Comparison FiniteSampling
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] anchor BinaryMetricAnchor.run BinaryIntegralRecovery.Guesses.run recoveryParams demand budget
variable {n : ℕ}
lemma demand_bound_s238r (Q : Polynomial ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ k : ℕ)
    (g : List Bool) (r : ℕ) (hr : r≤F.card)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F r)=BinaryFinSet.encode S) :
    (R.budget Q).eval (R.pack δ D F S Δ g []).length≤(budget Q).eval (pack δ D F Δ k g []).length := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

end OAI
end
