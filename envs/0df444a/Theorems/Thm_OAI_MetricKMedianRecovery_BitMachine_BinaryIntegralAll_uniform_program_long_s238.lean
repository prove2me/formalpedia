-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralAll_uniform_program_long_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.uniform_program_long_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:22:44.586558+00:00
-- url     : https://prove2.me/theorems/391da068-6cb0-4f4c-ad44-4ade8403516a
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.uniform_program_long_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.uniform_program_long` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralUniform.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralUniform.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll`, with `open LocalSearch Anchoring Completion Sampling Sampling.Comparison FiniteSampling IntegralAssembly IntegralCandidates Surplus`):
--
--   ```lean
--   theorem uniform_program_long_s238 (e : ℕ) : ∃ v : ℚ, ∃ C : ℕ, ∃ Q : Polynomial ℕ, ∃ d : ℕ,
--       ∀ {n : ℕ} [MetricSpace (Fin n)] (δ : Fin n→Fin n→ℕ)
--       (_hδ : ∀ i j,(δ i j:ℝ)=dist i j) (D F : Finset (Fin n)) (k : ℕ)
--       (_hD : D.Nonempty) (_hk : 0<k) (_hkF : k≤F.card)
--       (_hbound : ∀ x,∀ f∈F,δ x f≤ Rounding.cap D.card (gamma/16))
--       (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
--       (g : List Bool) (_hg : D.card+F.card≤g.length),
--       let M := Rounding.cap D.card (gamma/16)
--       let N := D.card+F.card
--       let δQ := fun i j=>(δ i j:ℚ)
--       let K := (Dsp.budget Q).eval (Dsp.pack δQ D F M k g []).length
--       ∃ S : Finset (Fin n),
--         (∀ seed:Fin K→Bool,run v C Q d (Dsp.pack δQ D F M k g (List.ofFn seed))=
--           BinaryFinSet.encode (output v C Q d δQ D F S M k g (List.ofFn seed))) ∧
--         (∀ seed:Fin K→Bool,output v C Q d δQ D F S M k g (List.ofFn seed)⊆F ∧
--           (output v C Q d δQ D F S M k g (List.ofFn seed)).Nonempty ∧
--           (output v C Q d δQ D F S M k g (List.ofFn seed)).card≤k ∧
--           realCost D (output v C Q d δQ D F S M k g (List.ofFn seed))≤5*optimum F D k) ∧
--         (1-FailureBudget.failure gamma e N≤ probability
--           (fun seed:Fin K→Bool=>realCost D (output v C Q d δQ D F S M k g (List.ofFn seed))≤
--             (2-gamma)*(1+gamma/16)*optimum F D k)) ∧
--         average (fun seed:Fin K→Bool=>realCost D (output v C Q d δQ D F S M k g (List.ofFn seed)))≤
--           ((2-gamma)*(1+gamma/16)+5*FailureBudget.failure gamma e N)*optimum F D k
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.FiniteSampling.average` and `OAI.MetricKMedianRecovery.FiniteSampling.probability` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Rounding.cap` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.Completion.realCost` and `OAI.MetricKMedianRecovery.FailureBudget.failure` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.LocalSearch.optimum` (definitions bundle `Q238K015` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.Dsp.pack` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.output`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.run` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.Dsp.budget` (definitions bundle `Q238K053` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalRounding.rounded_program_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralUniform.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.uniform_program_long)

import Mathlib
import Definitions.Def_Q238K053

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open LocalSearch Anchoring Completion Sampling Sampling.Comparison FiniteSampling IntegralAssembly IntegralCandidates Surplus
attribute [local irreducible] output BinaryIntegralDispatch.output BinaryIntegralDispatch.budget
  BinaryIntegralRecovery.Guesses.budget BinaryIntegralRecovery.Guesses.output BinaryMetricAnchor.run

theorem uniform_program_long_s238 (e : ℕ) : ∃ v : ℚ, ∃ C : ℕ, ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ {n : ℕ} [MetricSpace (Fin n)] (δ : Fin n→Fin n→ℕ)
    (_hδ : ∀ i j,(δ i j:ℝ)=dist i j) (D F : Finset (Fin n)) (k : ℕ)
    (_hD : D.Nonempty) (_hk : 0<k) (_hkF : k≤F.card)
    (_hbound : ∀ x,∀ f∈F,δ x f≤ Rounding.cap D.card (gamma/16))
    (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (g : List Bool) (_hg : D.card+F.card≤g.length),
    let M := Rounding.cap D.card (gamma/16)
    let N := D.card+F.card
    let δQ := fun i j=>(δ i j:ℚ)
    let K := (Dsp.budget Q).eval (Dsp.pack δQ D F M k g []).length
    ∃ S : Finset (Fin n),
      (∀ seed:Fin K→Bool,run v C Q d (Dsp.pack δQ D F M k g (List.ofFn seed))=
        BinaryFinSet.encode (output v C Q d δQ D F S M k g (List.ofFn seed))) ∧
      (∀ seed:Fin K→Bool,output v C Q d δQ D F S M k g (List.ofFn seed)⊆F ∧
        (output v C Q d δQ D F S M k g (List.ofFn seed)).Nonempty ∧
        (output v C Q d δQ D F S M k g (List.ofFn seed)).card≤k ∧
        realCost D (output v C Q d δQ D F S M k g (List.ofFn seed))≤5*optimum F D k) ∧
      (1-FailureBudget.failure gamma e N≤ probability
        (fun seed:Fin K→Bool=>realCost D (output v C Q d δQ D F S M k g (List.ofFn seed))≤
          (2-gamma)*(1+gamma/16)*optimum F D k)) ∧
      average (fun seed:Fin K→Bool=>realCost D (output v C Q d δQ D F S M k g (List.ofFn seed)))≤
        ((2-gamma)*(1+gamma/16)+5*FailureBudget.failure gamma e N)*optimum F D k := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

end OAI
end
