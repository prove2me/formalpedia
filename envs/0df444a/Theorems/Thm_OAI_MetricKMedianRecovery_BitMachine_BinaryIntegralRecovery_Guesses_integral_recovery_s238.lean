-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Guesses_integral_recovery_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.integral_recovery_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:16:21.964757+00:00
-- url     : https://prove2.me/theorems/ccb1d29f-723b-4838-a866-a43aa1305f67
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.integral_recovery_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.integral_recovery` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryAll.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryAll.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses`, with `open Completion Sampling Sampling.Comparison FiniteSampling`):
--
--   ```lean
--   lemma integral_recovery_s238 (A : ℝ) (e : ℕ) : ∃ Q : Polynomial ℕ, ∃ d : ℕ,
--       ∀ {n : ℕ} [PseudoMetricSpace (Fin n)]
--       (δ : Fin n→Fin n→ℕ) (_hδ : ∀ i j,(δ i j:ℝ)=dist i j)
--       (D F S O : Finset (Fin n)) (C : Comparison D S O) (_hD : D.Nonempty)
--       (_hSF : S⊆F) (_hOF : O⊆F) (_hS : S.Nonempty)
--       (Δ : ℕ) (_hΔ : 1≤Δ) (_hcap : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16))
--       (_hbound : ∀ x,∀ f∈F,δ x f≤Δ)
--       (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
--       (N : ℕ) (g : List Bool) (_hN : N≤g.length) (_hlog : (C.bad.card:ℝ)≤A*Real.log ((N:ℝ)+2)),
--       let δQ := fun i j=>(δ i j:ℚ)
--       let K := (budget Q).eval (pack δQ D F S Δ g []).length
--       (∀ seed:Fin K→Bool,run Q d (pack δQ D F S Δ g (List.ofFn seed))=
--         BinaryFinSet.encode (output Q d δQ D F S Δ g (List.ofFn seed))) ∧
--       (∀ seed:Fin K→Bool,output Q d δQ D F S Δ g (List.ofFn seed)⊆F ∧
--         (output Q d δQ D F S Δ g (List.ofFn seed)).Nonempty ∧
--         (output Q d δQ D F S Δ g (List.ofFn seed)).card≤S.card ∧
--         realCost D (output Q d δQ D F S Δ g (List.ofFn seed)) ≤ realCost D S) ∧
--       (1-FailureBudget.failure IntegralAssembly.gamma e N≤probability
--         (fun seed:Fin K→Bool=>realCost D (output Q d δQ D F S Δ g (List.ofFn seed))≤
--           (197/100:ℝ)*comparisonCost D C.assign)) ∧
--       average (fun seed:Fin K→Bool=>realCost D (output Q d δQ D F S Δ g (List.ofFn seed)))≤
--         (197/100:ℝ)*comparisonCost D C.assign+realCost D S*FailureBudget.failure IntegralAssembly.gamma e N
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.FiniteSampling.average` and `OAI.MetricKMedianRecovery.FiniteSampling.probability` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Rounding.cap` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.Completion.realCost`, `OAI.MetricKMedianRecovery.FailureBudget.failure`, `OAI.MetricKMedianRecovery.Sampling.Comparison` and `OAI.MetricKMedianRecovery.Sampling.comparisonCost` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.bad` (definitions bundle `Q238K015` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.pack` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.output` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.run` (definitions bundle `Q238K040` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.budget` (definitions bundle `Q238K049` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.designated_recovery_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryAll.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.integral_recovery)

import Mathlib
import Definitions.Def_Q238K049

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open Completion Sampling Sampling.Comparison FiniteSampling
attribute [local irreducible] output Repeat.output budget Fair.pack

lemma integral_recovery_s238 (A : ℝ) (e : ℕ) : ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ {n : ℕ} [PseudoMetricSpace (Fin n)]
    (δ : Fin n→Fin n→ℕ) (_hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (_hD : D.Nonempty)
    (_hSF : S⊆F) (_hOF : O⊆F) (_hS : S.Nonempty)
    (Δ : ℕ) (_hΔ : 1≤Δ) (_hcap : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16))
    (_hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (N : ℕ) (g : List Bool) (_hN : N≤g.length) (_hlog : (C.bad.card:ℝ)≤A*Real.log ((N:ℝ)+2)),
    let δQ := fun i j=>(δ i j:ℚ)
    let K := (budget Q).eval (pack δQ D F S Δ g []).length
    (∀ seed:Fin K→Bool,run Q d (pack δQ D F S Δ g (List.ofFn seed))=
      BinaryFinSet.encode (output Q d δQ D F S Δ g (List.ofFn seed))) ∧
    (∀ seed:Fin K→Bool,output Q d δQ D F S Δ g (List.ofFn seed)⊆F ∧
      (output Q d δQ D F S Δ g (List.ofFn seed)).Nonempty ∧
      (output Q d δQ D F S Δ g (List.ofFn seed)).card≤S.card ∧
      realCost D (output Q d δQ D F S Δ g (List.ofFn seed)) ≤ realCost D S) ∧
    (1-FailureBudget.failure IntegralAssembly.gamma e N≤probability
      (fun seed:Fin K→Bool=>realCost D (output Q d δQ D F S Δ g (List.ofFn seed))≤
        (197/100:ℝ)*comparisonCost D C.assign)) ∧
    average (fun seed:Fin K→Bool=>realCost D (output Q d δQ D F S Δ g (List.ofFn seed)))≤
      (197/100:ℝ)*comparisonCost D C.assign+realCost D S*FailureBudget.failure IntegralAssembly.gamma e N := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

end OAI
end
