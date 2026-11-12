-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Repeat_amplified_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.amplified_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:49:24.38638+00:00
-- url     : https://prove2.me/theorems/488267c7-3136-4042-93e0-65f3fe675576
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.amplified_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.amplified` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryAmplified.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryAmplified.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat`, with `open Completion Sampling Sampling.Comparison FiniteSampling`):
--
--   ```lean
--   lemma amplified_s238r (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
--       (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty)
--       (Δ : ℕ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (P : ℚ) (m : ℕ) (hm : m≤n) (r0 y0 : Fin n)
--       {B p ζ : ℝ} (hB : 0≤B) (hp : 0<p)
--       (hsuccess : p≤probability (fun seed:Fin (Fair.count D Δ m)→Bool=>realCost D
--         (Fair.output δ D F S Δ P m hm r0 y0 seed)≤B)) (hζ : 0<ζ)
--       (t : ℕ) (ht : Real.log (1/ζ)/p≤(t:ℝ)) :
--       (∀ seed:Fin t→Fin (Fair.count D Δ m)→Bool,realCost D (output δ D F S Δ P m hm r0 y0 t seed) ≤ realCost D S) ∧
--       1-ζ≤probability (fun seed:Fin t→Fin (Fair.count D Δ m)→Bool=>realCost D (output δ D F S Δ P m hm r0 y0 t seed)≤B) ∧
--       average (fun seed:Fin t→Fin (Fair.count D Δ m)→Bool=>realCost D (output δ D F S Δ P m hm r0 y0 t seed))≤B+realCost D S*ζ
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.FiniteSampling.average` and `OAI.MetricKMedianRecovery.FiniteSampling.probability` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.Completion.realCost` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.output` (definitions bundle `Q238L030` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.polynomial_program_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryAmplified.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.amplified)

import Mathlib
import Definitions.Def_Q238L030

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat
open Completion Sampling Sampling.Comparison FiniteSampling
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma amplified_s238r (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty)
    (Δ : ℕ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (P : ℚ) (m : ℕ) (hm : m≤n) (r0 y0 : Fin n)
    {B p ζ : ℝ} (hB : 0≤B) (hp : 0<p)
    (hsuccess : p≤probability (fun seed:Fin (Fair.count D Δ m)→Bool=>realCost D
      (Fair.output δ D F S Δ P m hm r0 y0 seed)≤B)) (hζ : 0<ζ)
    (t : ℕ) (ht : Real.log (1/ζ)/p≤(t:ℝ)) :
    (∀ seed:Fin t→Fin (Fair.count D Δ m)→Bool,realCost D (output δ D F S Δ P m hm r0 y0 t seed) ≤ realCost D S) ∧
    1-ζ≤probability (fun seed:Fin t→Fin (Fair.count D Δ m)→Bool=>realCost D (output δ D F S Δ P m hm r0 y0 t seed)≤B) ∧
    average (fun seed:Fin t→Fin (Fair.count D Δ m)→Bool=>realCost D (output δ D F S Δ P m hm r0 y0 t seed))≤B+realCost D S*ζ := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

end OAI
end
