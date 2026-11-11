-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Fair_output_success_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:39:25.97621+00:00
-- url     : https://prove2.me/theorems/c22b9810-1e19-49bc-9cd8-49766fbb9b3d
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryDemand.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryDemand.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair`, with `open Completion Sampling Sampling.Comparison FiniteSampling`):
--
--   ```lean
--   lemma output_success_s238 (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
--       (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
--       (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
--       (Δ : ℕ) (hΔ : 1≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
--       (P : ℚ) (hPeq : (P:ℝ)=comparisonCost D C.assign)
--       (hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
--       (hP : 0 < comparisonCost D C.assign) (hm0 : 0<C.bad.card)
--       (hm : C.bad.card≤n) (r0 y0 : Fin n) :
--       ((1/2:ℝ)^(2*C.bad.card)*samplingBound C.bad.card)*
--         ((1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ))≤
--         probability (fun seed:Fin (count D Δ C.bad.card)→Bool=>realCost D
--           (output δ D F S Δ P C.bad.card hm r0 y0 seed)≤(197/100:ℝ)*comparisonCost D C.assign)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.FiniteSampling.probability` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Completion.realCost`, `OAI.MetricKMedianRecovery.Sampling.Comparison` and `OAI.MetricKMedianRecovery.Sampling.comparisonCost` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.bad` (definitions bundle `Q238K015` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.samplingBound` (definitions bundle `Q238K023` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.count` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output` (definitions bundle `Q238K026` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.polynomial_program_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryDemand.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success)

import Mathlib
import Definitions.Def_Q238K023
import Definitions.Def_Q238K026

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open Completion Sampling Sampling.Comparison FiniteSampling
variable {n : ℕ}
variable [PseudoMetricSpace (Fin n)]
lemma output_success_s238 (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
    (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
    (Δ : ℕ) (hΔ : 1≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (P : ℚ) (hPeq : (P:ℝ)=comparisonCost D C.assign)
    (hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (hP : 0 < comparisonCost D C.assign) (hm0 : 0<C.bad.card)
    (hm : C.bad.card≤n) (r0 y0 : Fin n) :
    ((1/2:ℝ)^(2*C.bad.card)*samplingBound C.bad.card)*
      ((1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ))≤
      probability (fun seed:Fin (count D Δ C.bad.card)→Bool=>realCost D
        (output δ D F S Δ P C.bad.card hm r0 y0 seed)≤(197/100:ℝ)*comparisonCost D C.assign) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair

end OAI
end
