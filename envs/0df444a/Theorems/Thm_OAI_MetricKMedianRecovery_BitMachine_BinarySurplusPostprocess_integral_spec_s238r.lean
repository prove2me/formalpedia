-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySurplusPostprocess_integral_spec_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:00:55.048524+00:00
-- url     : https://prove2.me/theorems/8e8dc723-eadd-4589-b5ed-d52057cb3c54
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec` of [lean/OAI/Combinatorics/KMedianRecovery/Strictness/SurplusPostprocess.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/SurplusPostprocess.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess`, with `open WordOperations WordList BinaryArithmetic RationalLeaves`, `open BinaryOpeningPayment (field field_computes field_encode)`, `open BinaryFiniteContext (labels setBits)`):
--
--   ```lean
--   lemma integral_spec_s238r [MetricSpace (Fin m)] (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
--       (hloc : Function.Injective loc) (F S : Finset (Fin m)) (k : ℕ) (hSF : S⊆F) (hS : S.Nonempty)
--       (hkF : k≤F.card) (hδ : ∀ j,∀ i∈F,(δ (loc j) i:ℝ)=dist (loc j) i)
--       (hM : ∀ j,∀ i∈F,δ (loc j) i≤Rounding.cap d (IntegralAssembly.gamma/16)) :
--       ∃ T : Finset (Fin m),run (pack (fun i j=>(δ (loc j) i:ℚ)) F S k)=BinaryFinSet.encode T ∧
--         T⊆F ∧ T.Nonempty ∧ T.card=max k S.card ∧
--         LocalSearch.cost (Finset.univ.image loc) T≤LocalSearch.cost (Finset.univ.image loc) S ∧
--         LocalSearch.WidthLocalMin F (Finset.univ.image loc) T 5
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Rounding.cap` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.LocalSearch.WidthLocalMin` and `OAI.MetricKMedianRecovery.LocalSearch.cost` (definitions bundle `Q238L010` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.pack` (definitions bundle `Q238L031` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.run` (definitions bundle `Q238L034` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.produce_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/SurplusPostprocess.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec)

import Mathlib
import Definitions.Def_Q238L031
import Definitions.Def_Q238L034

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
lemma integral_spec_s238r [MetricSpace (Fin m)] (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
    (hloc : Function.Injective loc) (F S : Finset (Fin m)) (k : ℕ) (hSF : S⊆F) (hS : S.Nonempty)
    (hkF : k≤F.card) (hδ : ∀ j,∀ i∈F,(δ (loc j) i:ℝ)=dist (loc j) i)
    (hM : ∀ j,∀ i∈F,δ (loc j) i≤Rounding.cap d (IntegralAssembly.gamma/16)) :
    ∃ T : Finset (Fin m),run (pack (fun i j=>(δ (loc j) i:ℚ)) F S k)=BinaryFinSet.encode T ∧
      T⊆F ∧ T.Nonempty ∧ T.card=max k S.card ∧
      LocalSearch.cost (Finset.univ.image loc) T≤LocalSearch.cost (Finset.univ.image loc) S ∧
      LocalSearch.WidthLocalMin F (Finset.univ.image loc) T 5 := by
  sorry
end MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess

end OAI
end
