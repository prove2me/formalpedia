-- Prove2me | Theorems.Thm_OAI_SKRatio_Planted_ratio_cutoff_of_planted_form
-- name    : OAI.SKRatio.Planted.ratio_cutoff_of_planted_form
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T22:19:00.876905+00:00
-- url     : https://prove2.me/theorems/4e10bbc3-45cd-4913-a4eb-5ca60c76534c
-- title:
--   OAI.SKRatio.Planted.ratio_cutoff_of_planted_form: intermediate lemma from OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKRatio.Planted.ratio_cutoff_of_planted_form` of [lean/OAI/Probability/SKRatio/Gaussian/PlantedCriterion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Gaussian/PlantedCriterion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKRatio.Planted`, with `open scoped BigOperators Topology`, `open MeasureTheory ProbabilityTheory Real Filter`, `open Calculus`):
--
--   ```lean
--   theorem ratio_cutoff_of_planted_form (β ε η : ℝ)
--       (hβ : 0 ≤ β) (hβhalf : β < 1/2)
--       (hε : 0 < ε) (hεhalf : ε < 1/2) (hη : 0 < η)
--       {ρ κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ)
--       (hplant : ∀ᶠ n : ℕ in atTop,
--         law β n (formBad ρ n) ≤ ENNReal.ofReal (exp (-κ*n))) :
--       Tendsto (fun n : ℕ => disorderLaw β n
--           {g : Disorder n | 1+η <
--             (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)}) atTop (𝓝 0) ∧
--       (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1-ε))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKRatio.Planted.law` (definitions bundle `OAIQ024S008` of this split); `OAI.SKRatio.Planted.formBad` (definitions bundle `OAIQ024S016` of this split); `OAI.SKRatio.Disorder`, `OAI.SKRatio.Edge`, `OAI.SKRatio.disorderLaw` and `OAI.SKRatio.mixingTime` (the published bundle `Def_SKRatio`).
--
--   **Used by.** The proof of `OAI.SKRatio.Planted.ratio_cutoff_of_scalar` of this split imports it.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Gaussian/PlantedCriterion.lean (declaration OAI.SKRatio.Planted.ratio_cutoff_of_planted_form)

import Mathlib
import Definitions.Def_SKRatio
import Definitions.Def_OAIQ024S016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Planted
open Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem ratio_cutoff_of_planted_form (β ε η : ℝ)
    (hβ : 0 ≤ β) (hβhalf : β < 1/2)
    (hε : 0 < ε) (hεhalf : ε < 1/2) (hη : 0 < η)
    {ρ κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ)
    (hplant : ∀ᶠ n : ℕ in atTop,
      law β n (formBad ρ n) ≤ ENNReal.ofReal (exp (-κ*n))) :
    Tendsto (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1+η <
          (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)}) atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1-ε)) := by
  sorry

end SKRatio.Planted

end
end

end OAI
end
