-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_HeterogeneousMarks_parameter_dictionary_palm_sat
-- name    : OAI.DilutedSpinGlass.HeterogeneousMarks.parameter_dictionary_palm_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:18:13.642292+00:00
-- url     : https://prove2.me/theorems/f76a51aa-68ef-41d9-9361-b7c9f7bc7d1c
-- title:
--   OAI.DilutedSpinGlass.HeterogeneousMarks.parameter_dictionary_palm_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.HeterogeneousMarks.parameter_dictionary_palm` of [lean/OAI/Probability/DilutedSpin/ParameterPalm.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/ParameterPalm.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.HeterogeneousMarks`, with `open _root_.MeasureTheory ProbabilityTheory Set`, `open scoped NNReal BigOperators`):
--
--   ```lean
--   theorem parameter_dictionary_palm_sat
--       (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
--       {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
--       (hab : ∀ j, a j ≤ b j) (hI : ∀ j, Icc (a j) (b j) ⊆ Icc (-(1:ℝ)/4) (1/4))
--       (ht : ∀ j, |t j| ≤ 1/4)
--       (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
--       (hc : 0 < ν.real {j}) (hs : 0 < s) :
--       |externalCovariance ξ μ (ν.prod τ) (τ.map (fun q => (j,q))) r s S anchor T Q m base
--         (parameterFactor Prod.fst a b t D E u) D E f (t j) (boundParameter (a j) (b j) (u j))| ≤
--         B * (parameterError ξ μ (ν.prod τ) r s T Q (fun l => m l.succ) base
--           Prod.fst a b t D E j u / (ν.real {j}*(s:ℝ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.FiniteLaw`, `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.PrescribedTree`, `OAI.DilutedSpinGlass.RootPath`, `OAI.DilutedSpinGlass.boundParameter`, `OAI.DilutedSpinGlass.rootPathMeasurable`, `OAI.DilutedSpinGlass.HeterogeneousMarks.externalCovariance`, `OAI.DilutedSpinGlass.HeterogeneousMarks.parameterError`, `OAI.DilutedSpinGlass.HeterogeneousMarks.parameterFactor` and `OAI.DilutedSpinGlass.PrescribedTree.Leaf` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/ParameterPalm.lean (declaration OAI.DilutedSpinGlass.HeterogeneousMarks.parameter_dictionary_palm)

import Mathlib
import Definitions.Def_OAIQ041D000

section

attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
variable {Ω J Z X Y : Type} [Fintype Ω]
    [Countable J] [MeasurableSpace J] [MeasurableSingletonClass J] [DecidableEq J]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    {A : J × Z → Type} [∀ i, Fintype (A i)]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure J) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (anchor : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : J × Z) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (a b t : J → ℝ) (D E : (i : J × Z) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (j : J) (u : J → ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

theorem parameter_dictionary_palm_sat
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hab : ∀ j, a j ≤ b j) (hI : ∀ j, Icc (a j) (b j) ⊆ Icc (-(1:ℝ)/4) (1/4))
    (ht : ∀ j, |t j| ≤ 1/4)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (hc : 0 < ν.real {j}) (hs : 0 < s) :
    |externalCovariance ξ μ (ν.prod τ) (τ.map (fun q => (j,q))) r s S anchor T Q m base
      (parameterFactor Prod.fst a b t D E u) D E f (t j) (boundParameter (a j) (b j) (u j))| ≤
      B * (parameterError ξ μ (ν.prod τ) r s T Q (fun l => m l.succ) base
        Prod.fst a b t D E j u / (ν.real {j}*(s:ℝ))) := by
  sorry

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end
