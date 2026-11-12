-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryMetricAnchor_produce_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:04:38.682722+00:00
-- url     : https://prove2.me/theorems/e3cb8366-a236-4de5-bbab-9b9d83798e6b
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce` of [lean/OAI/Combinatorics/KMedianRecovery/Geometry/MetricAnchor.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/MetricAnchor.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor`, with `open WordOperations WordList RationalLeaves`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma produce_s238r [MetricSpace (Fin n)] (δ : Fin n→Fin n→ℕ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
--       (D F : Finset (Fin n)) (r : ℕ) (hr : 0 < r) (hrF : r≤F.card)
--       (hcap : ∀ p∈D,∀ i∈F,δ p i≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
--       ∃ S : Finset (Fin n),run (pack (fun i j=>(δ i j:ℚ)) D F r)=BinaryFinSet.encode S ∧
--         S⊆F ∧ S.Nonempty ∧ S.card=r ∧ LocalSearch.WidthLocalMin F D S 5 ∧
--         ∀ O : Finset (Fin n),O.Nonempty→O⊆F→O.card ≤ r→LocalSearch.cost D S≤5*LocalSearch.cost D O
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Rounding.cap` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.LocalSearch.WidthLocalMin` and `OAI.MetricKMedianRecovery.LocalSearch.cost` (definitions bundle `Q238L010` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.pack` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.run` (definitions bundle `Q238L037` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.finite_program_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/MetricAnchor.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce)

import Mathlib
import Definitions.Def_Q238L037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricAnchor
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryLocalAnchor.run BinaryProjection.run BinaryMetricArrays.run
variable {n : ℕ}
attribute [local irreducible] WordList.map
attribute [local semireducible] WordList.map
lemma produce_s238r [MetricSpace (Fin n)] (δ : Fin n→Fin n→ℕ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F : Finset (Fin n)) (r : ℕ) (hr : 0 < r) (hrF : r≤F.card)
    (hcap : ∀ p∈D,∀ i∈F,δ p i≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    ∃ S : Finset (Fin n),run (pack (fun i j=>(δ i j:ℚ)) D F r)=BinaryFinSet.encode S ∧
      S⊆F ∧ S.Nonempty ∧ S.card=r ∧ LocalSearch.WidthLocalMin F D S 5 ∧
      ∀ O : Finset (Fin n),O.Nonempty→O⊆F→O.card ≤ r→LocalSearch.cost D S≤5*LocalSearch.cost D O := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryMetricAnchor

end OAI
end
