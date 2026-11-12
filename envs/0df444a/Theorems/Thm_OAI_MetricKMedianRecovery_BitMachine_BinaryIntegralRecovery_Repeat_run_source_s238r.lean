-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Repeat_run_source_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.run_source_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:09:07.482862+00:00
-- url     : https://prove2.me/theorems/7528e377-ee05-42b9-a19f-650e61a65e3a
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.run_source_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.run_source` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryRepeat.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryRepeat.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat`, with `open WordOperations WordList Sampling.Comparison`):
--
--   ```lean
--   lemma run_source_s238r (A : ℝ) : ∃ d : ℕ, ∀ (Q : Polynomial ℕ) {n : ℕ} (δ : Fin n→Fin n→ℚ)
--       (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) (hm : m≤n),
--       Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16) → ∀ (extra : List Bool) (N : ℕ),
--       N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) → ∀ (r0 y0 : Fin n)
--       (seed : Fin (Q.eval extra.length)→Fin (Fair.count D Δ m)→Bool),
--       run Q d (Fair.pack δ D F S Δ P m extra (BinarySeed.raw (ds:=[Q.eval extra.length]) seed))=
--         BinaryFinSet.encode (output δ D F S Δ P m hm r0 y0 (Q.eval extra.length) seed)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Rounding.cap` and `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.raw` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.pack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.output` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.run` (definitions bundle `Q238L040` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.polynomial_program_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryRepeat.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.run_source)

import Mathlib
import Definitions.Def_Q238L040

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat
open WordOperations WordList Sampling.Comparison
attribute [local irreducible] extra Fair.raw Fair.demandWord Fair.run BinaryMetricBest.run RawUnary.run BinarySeed.rows
  BinaryIntegralRecovery.result BinaryFinSet.encode BinarySampler.Parameters.pack BinaryMetricBest.best Fair.output List.ofFn BinarySeed.raw
attribute [local irreducible] mapWith
variable {n : ℕ}
lemma run_source_s238r (A : ℝ) : ∃ d : ℕ, ∀ (Q : Polynomial ℕ) {n : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) (hm : m≤n),
    Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16) → ∀ (extra : List Bool) (N : ℕ),
    N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) → ∀ (r0 y0 : Fin n)
    (seed : Fin (Q.eval extra.length)→Fin (Fair.count D Δ m)→Bool),
    run Q d (Fair.pack δ D F S Δ P m extra (BinarySeed.raw (ds:=[Q.eval extra.length]) seed))=
      BinaryFinSet.encode (output δ D F S Δ P m hm r0 y0 (Q.eval extra.length) seed) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

end OAI
end
