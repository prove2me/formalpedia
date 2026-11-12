-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Repeat_polynomial_program_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.polynomial_program_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:08:13.197971+00:00
-- url     : https://prove2.me/theorems/0c8e701f-6e0d-42a3-b3d5-f94283266802
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.polynomial_program_s238r (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.polynomial_program` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryAmplified.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryAmplified.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat`, with `open Completion Sampling Sampling.Comparison FiniteSampling`, `open Polynomial`):
--
--   ```lean
--   lemma polynomial_program_s238r (A : ℝ) (e : ℕ) : ∃ Q : Polynomial ℕ, ∃ d : ℕ,
--       ∀ {n : ℕ} [PseudoMetricSpace (Fin n)]
--       (δ : Fin n→Fin n→ℚ) (_hδ : ∀ i j,(δ i j:ℝ)=dist i j)
--       (D F S O : Finset (Fin n)) (C : Comparison D S O) (_hD : D.Nonempty)
--       (_hSF : S⊆F) (_hOF : O⊆F) (_hS : S.Nonempty)
--       (Δ : ℕ) (_hΔ : 1≤Δ) (_hcap : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16))
--       (_hbound : ∀ x,∀ f∈F,δ x f≤Δ)
--       (P : ℚ) (_hPeq : (P:ℝ)=comparisonCost D C.assign)
--       (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
--       (_hP : 0 < comparisonCost D C.assign) (_hm0 : 0<C.bad.card)
--       (hm : C.bad.card≤n) (r0 y0 : Fin n) (N : ℕ) (g : List Bool)
--       (_hN : N≤g.length) (_hlog : (C.bad.card:ℝ)≤A*Real.log ((N:ℝ)+2)),
--       (∀ seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool,
--         run Q d (Fair.pack δ D F S Δ P C.bad.card g (BinarySeed.raw (ds:=[Q.eval g.length]) seed))=
--           BinaryFinSet.encode (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed)) ∧
--       (∀ seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool,
--         output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed⊆F ∧
--         (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed).card=S.card ∧
--         (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed).Nonempty) ∧
--       (1-FailureBudget.failure IntegralAssembly.gamma e N≤probability
--         (fun seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool=>
--           realCost D (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed)≤
--             (197/100:ℝ)*comparisonCost D C.assign)) ∧
--       average (fun seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool=>
--         realCost D (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed))≤
--           (197/100:ℝ)*comparisonCost D C.assign+realCost D S*FailureBudget.failure IntegralAssembly.gamma e N
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.FiniteSampling.average` and `OAI.MetricKMedianRecovery.FiniteSampling.probability` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.Rounding.cap` and `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.raw` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.Completion.realCost`, `OAI.MetricKMedianRecovery.FailureBudget.failure`, `OAI.MetricKMedianRecovery.Sampling.Comparison` and `OAI.MetricKMedianRecovery.Sampling.comparisonCost` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.bad` (definitions bundle `Q238L011` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.pack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.output` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.run` (definitions bundle `Q238L040` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.polynomial_recovery_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryAmplified.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.polynomial_program)

import Mathlib
import Definitions.Def_Q238L040

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat
open Completion Sampling Sampling.Comparison FiniteSampling
open Polynomial
lemma polynomial_program_s238r (A : ℝ) (e : ℕ) : ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ {n : ℕ} [PseudoMetricSpace (Fin n)]
    (δ : Fin n→Fin n→ℚ) (_hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (_hD : D.Nonempty)
    (_hSF : S⊆F) (_hOF : O⊆F) (_hS : S.Nonempty)
    (Δ : ℕ) (_hΔ : 1≤Δ) (_hcap : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16))
    (_hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (P : ℚ) (_hPeq : (P:ℝ)=comparisonCost D C.assign)
    (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (_hP : 0 < comparisonCost D C.assign) (_hm0 : 0<C.bad.card)
    (hm : C.bad.card≤n) (r0 y0 : Fin n) (N : ℕ) (g : List Bool)
    (_hN : N≤g.length) (_hlog : (C.bad.card:ℝ)≤A*Real.log ((N:ℝ)+2)),
    (∀ seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool,
      run Q d (Fair.pack δ D F S Δ P C.bad.card g (BinarySeed.raw (ds:=[Q.eval g.length]) seed))=
        BinaryFinSet.encode (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed)) ∧
    (∀ seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool,
      output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed⊆F ∧
      (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed).card=S.card ∧
      (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed).Nonempty) ∧
    (1-FailureBudget.failure IntegralAssembly.gamma e N≤probability
      (fun seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool=>
        realCost D (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed)≤
          (197/100:ℝ)*comparisonCost D C.assign)) ∧
    average (fun seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool=>
      realCost D (output δ D F S Δ P C.bad.card hm r0 y0 (Q.eval g.length) seed))≤
        (197/100:ℝ)*comparisonCost D C.assign+realCost D S*FailureBudget.failure IntegralAssembly.gamma e N := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

end OAI
end
