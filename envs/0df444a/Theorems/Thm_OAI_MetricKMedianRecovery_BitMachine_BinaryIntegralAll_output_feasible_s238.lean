-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralAll_output_feasible_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.output_feasible_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:20:21.473783+00:00
-- url     : https://prove2.me/theorems/fbfc7102-f9b6-426c-878b-25f0efd7d2ae
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.output_feasible_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.output_feasible` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralAll.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralAll.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll`, with `open WordOperations WordList`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma output_feasible_s238 (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→ Fin n→ℚ)
--       (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤ k) :
--       output v C Q d δ D F S Δ k g raw⊆F ∧ (output v C Q d δ D F S Δ k g raw).Nonempty ∧
--         (output v C Q d δ D F S Δ k g raw).card≤ k
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.output` (definitions bundle `Q238K053` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.finite_program_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralAll.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.output_feasible)

import Mathlib
import Definitions.Def_Q238K053

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
attribute [local irreducible] mapWith
lemma output_feasible_s238 (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→ Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤ k) :
    output v C Q d δ D F S Δ k g raw⊆F ∧ (output v C Q d δ D F S Δ k g raw).Nonempty ∧
      (output v C Q d δ D F S Δ k g raw).card≤ k := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

end OAI
end
