-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Guesses_ranges_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.ranges_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:55:08.447384+00:00
-- url     : https://prove2.me/theorems/da473aba-86c8-4f4c-afcd-15ade2373873
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.ranges_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.ranges_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryGuesses.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryGuesses.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses`, with `open WordOperations WordList`, `open BinaryOpeningPayment (field field_computes )`):
--
--   ```lean
--   lemma ranges_pack_s238 (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (g raw : List Bool)
--       (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
--       costRange (pack δ D F S Δ g raw)=encode (List.ofFn (fun p:Fin (D.card*Δ+1)=>p.val.bits)) ∧
--       countRange (pack δ D F S Δ g raw)=encode (List.ofFn (fun m:Fin (n+1)=>m.val.bits))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238K001` of this split); `OAI.MetricKMedianRecovery.Rounding.cap` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.countRange` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.pack` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.costRange` (definitions bundle `Q238K034` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.all_counts_budget_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.run_output_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralRecoveryGuesses.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.ranges_pack)

import Mathlib
import Definitions.Def_Q238K034

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open WordOperations WordList
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] BinaryFinSet.encode BinarySampler.Parameters.unary Count.run src
attribute [local irreducible] mapWith
variable {n : ℕ}
lemma ranges_pack_s238 (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (g raw : List Bool)
    (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    costRange (pack δ D F S Δ g raw)=encode (List.ofFn (fun p:Fin (D.card*Δ+1)=>p.val.bits)) ∧
    countRange (pack δ D F S Δ g raw)=encode (List.ofFn (fun m:Fin (n+1)=>m.val.bits)) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

end OAI
end
