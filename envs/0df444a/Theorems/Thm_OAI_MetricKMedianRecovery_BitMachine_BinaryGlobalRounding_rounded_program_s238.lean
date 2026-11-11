-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryGlobalRounding_rounded_program_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalRounding.rounded_program_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:17:55.660766+00:00
-- url     : https://prove2.me/theorems/9b3b3ad0-0446-404d-b04f-8f46d847b575
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalRounding.rounded_program_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalRounding.rounded_program` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalRoundMetric.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalRoundMetric.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalRounding`, with `open LocalSearch Completion IntegralAssembly FiniteSampling Sampling.Comparison BinaryTaggedSets`):
--
--   ```lean
--   theorem rounded_program_s238 (e : ℕ) : ∃ v : ℚ, ∃ C : ℕ, ∃ Q : Polynomial ℕ, ∃ d : ℕ,
--       ∀ (I : RationalMetricInput) (_hD : I.clients.Nonempty) (M : ℚ) (_hM : 0<M),
--       let K := (BinaryGlobalCall.A.budget Q).eval (BinaryGlobalCall.integralPack I M []).length
--       ∃ out : (Fin K→Bool)→Finset (Fin I.pointCount),
--         (∀ seed, BinaryGlobalCall.run v C Q d (BinaryGlobalCall.pack I M (List.ofFn seed))=BinaryFinSet.encode (out seed)) ∧
--         (∀ seed,(out seed)⊆I.facilities ∧ (out seed).Nonempty ∧ (out seed).card≤I.budget) ∧
--         ∀ O⊆I.facilities, O.Nonempty→O.card≤I.budget→
--           (M:ℝ)≤(I.cost O:ℝ)→(I.cost O:ℝ)≤I.clients.card*(M:ℝ)→
--           (∀ seed,(I.cost (out seed):ℝ)≤6*(I.cost O:ℝ)) ∧
--           1-FailureBudget.failure gamma e I.size≤probability
--             (fun seed=>(I.cost (out seed):ℝ)≤(2-gamma/2)*(I.cost O:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.FiniteSampling.probability` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.FailureBudget.failure` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.integralPack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.pack` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.A.budget` (definitions bundle `Q238K051` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.run` (definitions bundle `Q238K053` of this split); `OAI.MetricKMedianRecovery.RationalMetricInput`, `OAI.MetricKMedianRecovery.RationalMetricInput.cost` and `OAI.MetricKMedianRecovery.RationalMetricInput.size` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.finite_program_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalRoundMetric.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalRounding.rounded_program)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K053

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalRounding
open LocalSearch Completion IntegralAssembly FiniteSampling Sampling.Comparison BinaryTaggedSets
attribute [local irreducible] BinaryIntegralAll.output BinaryIntegralAll.run BinaryIntegralDispatch.budget
  BinaryGlobalCall.run

theorem rounded_program_s238 (e : ℕ) : ∃ v : ℚ, ∃ C : ℕ, ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ (I : RationalMetricInput) (_hD : I.clients.Nonempty) (M : ℚ) (_hM : 0<M),
    let K := (BinaryGlobalCall.A.budget Q).eval (BinaryGlobalCall.integralPack I M []).length
    ∃ out : (Fin K→Bool)→Finset (Fin I.pointCount),
      (∀ seed, BinaryGlobalCall.run v C Q d (BinaryGlobalCall.pack I M (List.ofFn seed))=BinaryFinSet.encode (out seed)) ∧
      (∀ seed,(out seed)⊆I.facilities ∧ (out seed).Nonempty ∧ (out seed).card≤I.budget) ∧
      ∀ O⊆I.facilities, O.Nonempty→O.card≤I.budget→
        (M:ℝ)≤(I.cost O:ℝ)→(I.cost O:ℝ)≤I.clients.card*(M:ℝ)→
        (∀ seed,(I.cost (out seed):ℝ)≤6*(I.cost O:ℝ)) ∧
        1-FailureBudget.failure gamma e I.size≤probability
          (fun seed=>(I.cost (out seed):ℝ)≤(2-gamma/2)*(I.cost O:ℝ)) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryGlobalRounding

end OAI
end
