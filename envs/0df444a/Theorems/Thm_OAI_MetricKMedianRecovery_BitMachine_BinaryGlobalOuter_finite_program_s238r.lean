-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryGlobalOuter_finite_program_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.finite_program_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:20:04.400378+00:00
-- url     : https://prove2.me/theorems/697dceeb-0775-4844-9286-f6d8f14ee105
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.finite_program_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.finite_program` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalOuterProbability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalOuterProbability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter`, with `open LocalSearch Completion IntegralAssembly FiniteSampling Sampling.Comparison`):
--
--   ```lean
--   theorem finite_program_s238r (e : ℕ) : ∃ v : ℚ, ∃ C : ℕ, ∃ Q : Polynomial ℕ, ∃ d : ℕ,
--       ∀ I : RationalMetricInput,
--         let K := (budget Q).eval I.bits.length
--         (∀ seed:Fin K→Bool,(I.cost (output v C Q d I (List.ofFn seed)):ℝ)≤6*(I.optimum:ℝ)) ∧
--         1-FailureBudget.failure gamma e I.size≤probability
--           (fun seed:Fin K→Bool=>(I.cost (output v C Q d I (List.ofFn seed)):ℝ)≤(2-gamma/2)*(I.optimum:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.FiniteSampling.probability` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.FailureBudget.failure` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.budget` and `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.output` (definitions bundle `Q238L054` of this split); `OAI.MetricKMedianRecovery.RationalMetricInput`, `OAI.MetricKMedianRecovery.RationalMetricInput.bits`, `OAI.MetricKMedianRecovery.RationalMetricInput.cost`, `OAI.MetricKMedianRecovery.RationalMetricInput.optimum` and `OAI.MetricKMedianRecovery.RationalMetricInput.size` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.global_application` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalOuterProbability.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.finite_program)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L054

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open LocalSearch Completion IntegralAssembly FiniteSampling Sampling.Comparison
attribute [local irreducible] BinaryGlobalCall.run BinaryIntegralAll.run BinaryIntegralDispatch.budget output words budget

theorem finite_program_s238r (e : ℕ) : ∃ v : ℚ, ∃ C : ℕ, ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ I : RationalMetricInput,
      let K := (budget Q).eval I.bits.length
      (∀ seed:Fin K→Bool,(I.cost (output v C Q d I (List.ofFn seed)):ℝ)≤6*(I.optimum:ℝ)) ∧
      1-FailureBudget.failure gamma e I.size≤probability
        (fun seed:Fin K→Bool=>(I.cost (output v C Q d I (List.ofFn seed)):ℝ)≤(2-gamma/2)*(I.optimum:ℝ)) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end
