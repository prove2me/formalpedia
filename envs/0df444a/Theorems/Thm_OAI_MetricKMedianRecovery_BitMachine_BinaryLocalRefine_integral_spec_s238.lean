-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryLocalRefine_integral_spec_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.integral_spec_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:49:51.197971+00:00
-- url     : https://prove2.me/theorems/cd312118-77b8-4b47-9eb4-0f2caa85aaf3
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.integral_spec_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.integral_spec` of [lean/OAI/Combinatorics/KMedianRecovery/Geometry/LocalRefineMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/LocalRefineMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine`, with `open RationalLeaves WordOperations WordList Polynomial`):
--
--   ```lean
--   lemma integral_spec_s238 {m d : ℕ} [MetricSpace (Fin m)] (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
--       (hloc : Function.Injective loc) (fs : List (Fin m)) (S : Finset (Fin m))
--       (hSF : S⊆fs.toFinset) (hS : S.Nonempty)
--       (hδ : ∀ j,∀ i∈fs.toFinset,(δ (loc j) i:ℝ)=dist (loc j) i)
--       (hM : ∀ j,∀ i∈fs.toFinset,δ (loc j) i≤Rounding.cap d (IntegralAssembly.gamma/16)) :
--       ∃ T : Finset (Fin m),run (pack (fun i j=>(δ (loc j) i:ℚ)) fs S)=BinaryFiniteContext.setBits (T.image original) ∧
--         T⊆fs.toFinset ∧ T.Nonempty ∧ T.card=S.card ∧
--         LocalSearch.cost (Finset.univ.image loc) T≤LocalSearch.cost (Finset.univ.image loc) S ∧
--         LocalSearch.WidthLocalMin fs.toFinset (Finset.univ.image loc) T 5
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Rounding.cap` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.LocalSearch.WidthLocalMin` and `OAI.MetricKMedianRecovery.LocalSearch.cost` (definitions bundle `Q238K015` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.original` (definitions bundle `Q238K017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.setBits` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.pack` (definitions bundle `Q238K026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.run` (definitions bundle `Q238K030` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/LocalRefineMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.integral_spec)

import Mathlib
import Definitions.Def_Q238K015
import Definitions.Def_Q238K030

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalRefine
open RationalLeaves WordOperations WordList Polynomial
lemma integral_spec_s238 {m d : ℕ} [MetricSpace (Fin m)] (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
    (hloc : Function.Injective loc) (fs : List (Fin m)) (S : Finset (Fin m))
    (hSF : S⊆fs.toFinset) (hS : S.Nonempty)
    (hδ : ∀ j,∀ i∈fs.toFinset,(δ (loc j) i:ℝ)=dist (loc j) i)
    (hM : ∀ j,∀ i∈fs.toFinset,δ (loc j) i≤Rounding.cap d (IntegralAssembly.gamma/16)) :
    ∃ T : Finset (Fin m),run (pack (fun i j=>(δ (loc j) i:ℚ)) fs S)=BinaryFiniteContext.setBits (T.image original) ∧
      T⊆fs.toFinset ∧ T.Nonempty ∧ T.card=S.card ∧
      LocalSearch.cost (Finset.univ.image loc) T≤LocalSearch.cost (Finset.univ.image loc) S ∧
      LocalSearch.WidthLocalMin fs.toFinset (Finset.univ.image loc) T 5 := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryLocalRefine

end OAI
end
