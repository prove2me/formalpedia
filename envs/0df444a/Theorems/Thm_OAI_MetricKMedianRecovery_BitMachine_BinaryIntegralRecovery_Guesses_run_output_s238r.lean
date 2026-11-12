-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Guesses_run_output_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.run_output_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:07:37.289877+00:00
-- url     : https://prove2.me/theorems/94df05b1-23f8-4788-8605-16afc9f10f1b
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.run_output_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.run_output` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoverySelection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoverySelection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses`, with `open Completion Sampling Sampling.Comparison FiniteSampling`):
--
--   ```lean
--   lemma run_output_s238r (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
--       (D F S : Finset (Fin n)) (Δ : ℕ) (g raw : List Bool)
--       (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
--       run Q d (pack δ D F S Δ g raw)=BinaryFinSet.encode (output Q d δ D F S Δ g raw)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Rounding.cap` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.pack` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.output` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.run` (definitions bundle `Q238L040` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.integral_recovery_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.polynomial_recovery_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoverySelection.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.run_output)

import Mathlib
import Definitions.Def_Q238L040

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open Completion Sampling Sampling.Comparison FiniteSampling
variable {n : ℕ}
lemma run_output_s238r (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℕ) (g raw : List Bool)
    (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    run Q d (pack δ D F S Δ g raw)=BinaryFinSet.encode (output Q d δ D F S Δ g raw) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

end OAI
end
