-- Prove2me | Theorems.Thm_OAI_SKRatio_Bins_random_binForm_tail
-- name    : OAI.SKRatio.Bins.random_binForm_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:25:26.375013+00:00
-- url     : https://prove2.me/theorems/d1593316-ab57-4a12-83e7-c66fa6a9b9d9
-- title:
--   OAI.SKRatio.Bins.random_binForm_tail: intermediate lemma from OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKRatio.Bins.random_binForm_tail` of [lean/OAI/Probability/SKRatio/Quantization/ConditionalBins.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Quantization/ConditionalBins.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKRatio.Bins`, with `open scoped BigOperators Matrix ENNReal`, `open MeasureTheory ProbabilityTheory Filter Real`, `open Planted Scalar SKRatioClock.Regression MatrixNet Calculus`):
--
--   ```lean
--   theorem random_binForm_tail {α : Type*} [Fintype α] [DecidableEq α]
--       [MeasurableSpace α] [MeasurableSingletonClass α]
--       {β K a C : ℝ} (hβ : 0<β) (hK : 0≤K) (ha : 0<a)
--       (h : α → ℝ) (q : ℝ → α) (hq : Measurable q) :
--       ∃ N : ℕ, ∀ {n : ℕ} (_hn : 0<n),
--         (standardArrayLaw (Fin n × Fin n)).real {g |
--           (∀ d, 2 ≤ count (fun i => q (augmentedField β g i)) d) ∧
--           (∀ z : Parameters α, finiteV β (binT (fun i => q (augmentedField β g i))) h z≤C) ∧
--           g ∈ binFormBad β h (fun i => q (augmentedField β g i)) K (C+2*a)} ≤
--         N*exp (-a^2*(n:ℝ)/(π^2*β^2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKRatio.Bins.Parameters`, `OAI.SKRatio.Bins.binFormBad`, `OAI.SKRatio.Bins.binT`, `OAI.SKRatio.Bins.count` and `OAI.SKRatio.Bins.finiteV` (definitions bundle `OAIQ024S000` of this split); `OAI.SKRatioClock.Regression.standardArrayLaw` (definitions bundle `OAIQ024S001` of this split); `OAI.SKRatio.Planted.augmentedField` (definitions bundle `OAIQ024S008` of this split).
--
--   **Used by.** The proof of `OAI.SKRatio.Planted.ratio_cutoff_of_scalar` of this split imports it.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Quantization/ConditionalBins.lean (declaration OAI.SKRatio.Bins.random_binForm_tail)

import Mathlib
import Definitions.Def_OAIQ024S008

section

attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix ENNReal
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression MatrixNet Calculus
attribute [local instance] Classical.propDecidable

theorem random_binForm_tail {α : Type*} [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {β K a C : ℝ} (hβ : 0<β) (hK : 0≤K) (ha : 0<a)
    (h : α → ℝ) (q : ℝ → α) (hq : Measurable q) :
    ∃ N : ℕ, ∀ {n : ℕ} (_hn : 0<n),
      (standardArrayLaw (Fin n × Fin n)).real {g |
        (∀ d, 2 ≤ count (fun i => q (augmentedField β g i)) d) ∧
        (∀ z : Parameters α, finiteV β (binT (fun i => q (augmentedField β g i))) h z≤C) ∧
        g ∈ binFormBad β h (fun i => q (augmentedField β g i)) K (C+2*a)} ≤
      N*exp (-a^2*(n:ℝ)/(π^2*β^2)) := by
  sorry

end SKRatio.Bins

end

end OAI
end
