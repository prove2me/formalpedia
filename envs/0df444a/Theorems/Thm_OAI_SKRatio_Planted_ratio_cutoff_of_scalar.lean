-- Prove2me | Theorems.Thm_OAI_SKRatio_Planted_ratio_cutoff_of_scalar
-- name    : OAI.SKRatio.Planted.ratio_cutoff_of_scalar
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T22:19:02.54309+00:00
-- url     : https://prove2.me/theorems/74ac03d3-9855-4814-9f39-a59cced2d420
-- title:
--   OAI.SKRatio.Planted.ratio_cutoff_of_scalar: intermediate lemma from OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKRatio.Planted.ratio_cutoff_of_scalar` of [lean/OAI/Probability/SKRatio/Variational/ScalarTransfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Variational/ScalarTransfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKRatio.Planted`, with `open scoped BigOperators Matrix NNReal ENNReal Topology`, `open MeasureTheory ProbabilityTheory Filter Real`, `open Bins Scalar SKRatioClock.Regression Calculus`):
--
--   ```lean
--   theorem ratio_cutoff_of_scalar (β ε η C : ℝ)
--       (hβ : 0 < β) (hβhalf : β < 1/2) (hε : 0 < ε) (hεhalf : ε < 1/2) (hη : 0 < η)
--       (hC : C < 1)
--       (hscalar : ∀ b r : ℝ → ℝ, MemLp b 2 (fieldLaw β) → MemLp r 2 (fieldLaw β) →
--         (∫ x, b x^2+r x^2 ∂fieldLaw β)=1 → variational β b r ≤ C) :
--       Tendsto (fun n : ℕ => disorderLaw β n
--           {g : Disorder n | 1+η  <  (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)}) atTop (𝓝 0) ∧
--       (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0  <  mixingTime g (1-ε))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKRatio.Scalar.fieldLaw` (definitions bundle `OAIQ024S001` of this split); `OAI.SKRatio.Scalar.variational` (definitions bundle `OAIQ024S016` of this split); `OAI.SKRatio.Disorder`, `OAI.SKRatio.Edge`, `OAI.SKRatio.disorderLaw` and `OAI.SKRatio.mixingTime` (the published bundle `Def_SKRatio`).
--
--   **Used by.** The proof of `OAI.SKRatio.ratio_cutoff` of this split imports it.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Variational/ScalarTransfer.lean (declaration OAI.SKRatio.Planted.ratio_cutoff_of_scalar)

import Mathlib
import Definitions.Def_SKRatio
import Definitions.Def_OAIQ024S016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real

namespace SKRatio.Planted
open Bins Scalar SKRatioClock.Regression Calculus
attribute [local instance] Classical.propDecidable

theorem ratio_cutoff_of_scalar (β ε η C : ℝ)
    (hβ : 0 < β) (hβhalf : β < 1/2) (hε : 0 < ε) (hεhalf : ε < 1/2) (hη : 0 < η)
    (hC : C < 1)
    (hscalar : ∀ b r : ℝ → ℝ, MemLp b 2 (fieldLaw β) → MemLp r 2 (fieldLaw β) →
      (∫ x, b x^2+r x^2 ∂fieldLaw β)=1 → variational β b r ≤ C) :
    Tendsto (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1+η  <  (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)}) atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0  <  mixingTime g (1-ε)) := by
  sorry

end SKRatio.Planted

end

end OAI
end
