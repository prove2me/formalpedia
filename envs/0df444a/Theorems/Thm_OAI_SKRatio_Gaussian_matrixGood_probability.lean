-- Prove2me | Theorems.Thm_OAI_SKRatio_Gaussian_matrixGood_probability
-- name    : OAI.SKRatio.Gaussian.matrixGood_probability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T22:18:39.811983+00:00
-- url     : https://prove2.me/theorems/d2dd7b6a-82f2-42c6-8bdf-0ee19a33149e
-- title:
--   OAI.SKRatio.Gaussian.matrixGood_probability: intermediate lemma from OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKRatio.Gaussian.matrixGood_probability` of [lean/OAI/Probability/SKRatio/Gaussian/GaussianEvents.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Gaussian/GaussianEvents.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKRatio.Gaussian`, with `open scoped BigOperators Topology ENNReal`, `open MeasureTheory ProbabilityTheory Real Filter`, `open Calculus`):
--
--   ```lean
--   theorem matrixGood_probability {β δ : ℝ} (hβ : 0 ≤ β) (hδ : 0 < δ) :
--       Tendsto (fun n : ℕ => disorderLaw β n (matrixGood β δ n)ᶜ) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKRatio.Gaussian.matrixGood` (definitions bundle `OAIQ024S016` of this split); `OAI.SKRatio.Disorder`, `OAI.SKRatio.Edge` and `OAI.SKRatio.disorderLaw` (the published bundle `Def_SKRatio`).
--
--   **Used by.** The proofs of `OAI.SKRatio.Planted.ratio_cutoff_of_planted_form` and `OAI.SKRatio.ratio_cutoff` of this split import it.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Gaussian/GaussianEvents.lean (declaration OAI.SKRatio.Gaussian.matrixGood_probability)

import Mathlib
import Definitions.Def_SKRatio
import Definitions.Def_OAIQ024S016

section

attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatio.Planted.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology ENNReal
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Gaussian
open Calculus
variable {n : ℕ}

theorem matrixGood_probability {β δ : ℝ} (hβ : 0 ≤ β) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => disorderLaw β n (matrixGood β δ n)ᶜ) atTop (𝓝 0) := by
  sorry

end SKRatio.Gaussian

end
end

end OAI
end
