-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralAll_lift_probability_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.lift_probability_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:20:43.960498+00:00
-- url     : https://prove2.me/theorems/3031287a-48a9-4106-8099-0fdf60ba7189
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.lift_probability_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.lift_probability` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralDispatchGuarantee.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralDispatchGuarantee.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll`, with `open Completion Sampling Sampling.Comparison FiniteSampling`):
--
--   ```lean
--   lemma lift_probability_s238r (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
--       (hδ : ∀ i j,(δ i j:ℝ)=dist i j) (D F S : Finset (Fin n)) (Δ k : ℕ) (g : List Bool)
--       (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k)
--       (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F k)=BinaryFinSet.encode S)
--       (B p : ℝ) (hp : p≤ probability (fun seed:Fin ((Dsp.budget Q).eval (Dsp.pack δ D F Δ k g []).length)→ Bool=>
--         realCost D (BinaryIntegralDispatch.output Q d δ D F S Δ k g (List.ofFn seed))≤ B)) :
--       p≤ probability (fun seed:Fin ((Dsp.budget Q).eval (Dsp.pack δ D F Δ k g []).length)→ Bool=>
--         realCost D (output v C Q d δ D F S Δ k g (List.ofFn seed))≤ B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.FiniteSampling.probability` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.Completion.realCost` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.pack` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.Dsp.pack` (definitions bundle `Q238L035` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.run` (definitions bundle `Q238L037` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.output` (definitions bundle `Q238L053` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.output` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.Dsp.budget` (definitions bundle `Q238L054` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.finite_program_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralDispatchGuarantee.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.lift_probability)

import Mathlib
import Definitions.Def_Q238L054

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open Completion Sampling Sampling.Comparison FiniteSampling
attribute [local irreducible] output BinaryIntegralDispatch.output BinaryIntegralDispatch.budget
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma lift_probability_s238r (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (hδ : ∀ i j,(δ i j:ℝ)=dist i j) (D F S : Finset (Fin n)) (Δ k : ℕ) (g : List Bool)
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F k)=BinaryFinSet.encode S)
    (B p : ℝ) (hp : p≤ probability (fun seed:Fin ((Dsp.budget Q).eval (Dsp.pack δ D F Δ k g []).length)→ Bool=>
      realCost D (BinaryIntegralDispatch.output Q d δ D F S Δ k g (List.ofFn seed))≤ B)) :
    p≤ probability (fun seed:Fin ((Dsp.budget Q).eval (Dsp.pack δ D F Δ k g []).length)→ Bool=>
      realCost D (output v C Q d δ D F S Δ k g (List.ofFn seed))≤ B) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

end OAI
end
