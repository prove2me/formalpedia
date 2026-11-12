-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralAll_finite_program_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.finite_program_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:23:03.977534+00:00
-- url     : https://prove2.me/theorems/ab293e91-0395-4c55-b1f3-3295ae746d89
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.finite_program_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.finite_program` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralProgram.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralProgram.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll`, with `open LocalSearch Anchoring Completion Sampling Sampling.Comparison FiniteSampling IntegralAssembly IntegralCandidates`):
--
--   ```lean
--   lemma finite_program_s238r (A : ℝ) (e : ℕ) : ∃ Q : Polynomial ℕ, ∃ d : ℕ,
--       ∀ {n : ℕ} [MetricSpace (Fin n)]
--       (δ : Fin n→Fin n→ℕ) (_hδ : ∀ i j,(δ i j:ℝ)=dist i j)
--       (D F : Finset (Fin n)) (k L M N C : ℕ) (v : ℚ)
--       (_hD : D.Nonempty) (_hk : 0<k) (_hL : 0<L) (_hkF : k≤ F.card)
--       (_hN : N=D.card+F.card) (_hM : 0<M)
--       (_hcap : M≤ Rounding.cap D.card (gamma/16))
--       (_hbound : ∀ x,∀ f∈F,δ x f≤ M) (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤ dist w f)
--       (_hv : (0:ℝ)<(v:ℝ)) (_hv1 : (v:ℝ)≤ 1/12)
--       (_hvc : (v:ℝ)≤ strictnessGap (200*countConstant (1/100))/1000)
--       (_hsmall : (v:ℝ)^2≤ strictnessGap (200*countConstant (1/100))/(6*(200*countConstant (1/100)+2)))
--       (_hsize : 2*L<k→ 2/(N:ℝ)≤ strictnessGap (200*countConstant (1/100))/200)
--       (_herror : 2*L<k→ (N:ℝ)^2/2^N≤ (v:ℝ))
--       (_hfree : 3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(D.card:ℝ)*(M:ℝ))+1)≤ L)
--       (_hC : 2≤ (1+v^2)^C) (g : List Bool) (_hg : N≤ g.length)
--       (_hlog : (countBound L:ℝ)≤ A*Real.log ((N:ℝ)+2)),
--       let δQ := fun i j=>(δ i j:ℚ)
--       let K := (Dsp.budget Q).eval (Dsp.pack δQ D F M k g []).length
--       ∃ S : Finset (Fin n),
--         (∀ seed:Fin K→Bool,run v C Q d (Dsp.pack δQ D F M k g (List.ofFn seed))=
--           BinaryFinSet.encode (output v C Q d δQ D F S M k g (List.ofFn seed))) ∧
--         (∀ seed:Fin K→Bool,output v C Q d δQ D F S M k g (List.ofFn seed)⊆F ∧
--           (output v C Q d δQ D F S M k g (List.ofFn seed)).Nonempty ∧
--           (output v C Q d δQ D F S M k g (List.ofFn seed)).card≤ k ∧
--           realCost D (output v C Q d δQ D F S M k g (List.ofFn seed))≤ 5*optimum F D k) ∧
--         (1-FailureBudget.failure gamma e N≤ probability
--           (fun seed:Fin K→Bool=>realCost D (output v C Q d δQ D F S M k g (List.ofFn seed))≤
--             (2-gamma)*(1+gamma/16)*optimum F D k)) ∧
--         average (fun seed:Fin K→Bool=>realCost D (output v C Q d δQ D F S M k g (List.ofFn seed)))≤
--           ((2-gamma)*(1+gamma/16)+5*FailureBudget.failure gamma e N)*optimum F D k
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Anchoring.countConstant` (definitions bundle `Q238L000` of this split); `OAI.MetricKMedianRecovery.FiniteSampling.average` and `OAI.MetricKMedianRecovery.FiniteSampling.probability` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.strictnessGap` and `OAI.MetricKMedianRecovery.Rounding.cap` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.Completion.realCost`, `OAI.MetricKMedianRecovery.FailureBudget.failure` and `OAI.MetricKMedianRecovery.HistoryPhaseBound.limit` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.LocalSearch.optimum` (definitions bundle `Q238L010` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.countBound` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.Dsp.pack` (definitions bundle `Q238L035` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.output`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.run` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.Dsp.budget` (definitions bundle `Q238L054` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.uniform_program_long_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralProgram.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.finite_program)

import Mathlib
import Definitions.Def_Q238L054

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open LocalSearch Anchoring Completion Sampling Sampling.Comparison FiniteSampling IntegralAssembly IntegralCandidates
attribute [local irreducible] output BinaryIntegralDispatch.output BinaryIntegralDispatch.budget
  BinaryIntegralRecovery.Guesses.budget BinaryIntegralRecovery.Guesses.output BinaryMetricAnchor.run

lemma finite_program_s238r (A : ℝ) (e : ℕ) : ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ {n : ℕ} [MetricSpace (Fin n)]
    (δ : Fin n→Fin n→ℕ) (_hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F : Finset (Fin n)) (k L M N C : ℕ) (v : ℚ)
    (_hD : D.Nonempty) (_hk : 0<k) (_hL : 0<L) (_hkF : k≤ F.card)
    (_hN : N=D.card+F.card) (_hM : 0<M)
    (_hcap : M≤ Rounding.cap D.card (gamma/16))
    (_hbound : ∀ x,∀ f∈F,δ x f≤ M) (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤ dist w f)
    (_hv : (0:ℝ)<(v:ℝ)) (_hv1 : (v:ℝ)≤ 1/12)
    (_hvc : (v:ℝ)≤ strictnessGap (200*countConstant (1/100))/1000)
    (_hsmall : (v:ℝ)^2≤ strictnessGap (200*countConstant (1/100))/(6*(200*countConstant (1/100)+2)))
    (_hsize : 2*L<k→ 2/(N:ℝ)≤ strictnessGap (200*countConstant (1/100))/200)
    (_herror : 2*L<k→ (N:ℝ)^2/2^N≤ (v:ℝ))
    (_hfree : 3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(D.card:ℝ)*(M:ℝ))+1)≤ L)
    (_hC : 2≤ (1+v^2)^C) (g : List Bool) (_hg : N≤ g.length)
    (_hlog : (countBound L:ℝ)≤ A*Real.log ((N:ℝ)+2)),
    let δQ := fun i j=>(δ i j:ℚ)
    let K := (Dsp.budget Q).eval (Dsp.pack δQ D F M k g []).length
    ∃ S : Finset (Fin n),
      (∀ seed:Fin K→Bool,run v C Q d (Dsp.pack δQ D F M k g (List.ofFn seed))=
        BinaryFinSet.encode (output v C Q d δQ D F S M k g (List.ofFn seed))) ∧
      (∀ seed:Fin K→Bool,output v C Q d δQ D F S M k g (List.ofFn seed)⊆F ∧
        (output v C Q d δQ D F S M k g (List.ofFn seed)).Nonempty ∧
        (output v C Q d δQ D F S M k g (List.ofFn seed)).card≤ k ∧
        realCost D (output v C Q d δQ D F S M k g (List.ofFn seed))≤ 5*optimum F D k) ∧
      (1-FailureBudget.failure gamma e N≤ probability
        (fun seed:Fin K→Bool=>realCost D (output v C Q d δQ D F S M k g (List.ofFn seed))≤
          (2-gamma)*(1+gamma/16)*optimum F D k)) ∧
      average (fun seed:Fin K→Bool=>realCost D (output v C Q d δQ D F S M k g (List.ofFn seed)))≤
        ((2-gamma)*(1+gamma/16)+5*FailureBudget.failure gamma e N)*optimum F D k := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

end OAI
end
