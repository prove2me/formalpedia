-- Prove2me | Theorems.Thm_OAI_SKRatio_Planted_reduced_error_rare
-- name    : OAI.SKRatio.Planted.reduced_error_rare
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:27:23.069868+00:00
-- url     : https://prove2.me/theorems/d7b06d63-32fb-4c1a-9cc4-b4bfaad54409
-- title:
--   OAI.SKRatio.Planted.reduced_error_rare: intermediate lemma from OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKRatio.Planted.reduced_error_rare` of [lean/OAI/Probability/SKRatio/Variational/ReducedForm.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Variational/ReducedForm.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKRatio.Planted`, with `open scoped BigOperators NNReal ENNReal Topology`, `open MeasureTheory ProbabilityTheory Filter Set Real`, `open SKRatioClock.Regression MatrixNet Calculus Scalar`):
--
--   ```lean
--   theorem reduced_error_rare {β : ℝ} (hβ : 0<β) {u : ℝ} (hu : 0<u) :
--       ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
--         (fun n => {g | ∃ p : Fin n → ℝ, u*(∑ i, p i^2)<
--           |gradientForm (coupling (augmentedDisorder β g)) p-reducedForm β g p|})
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKRatio.Calculus.gradientForm` (definitions bundle `OAIQ024S000` of this split); `OAI.SKRatioClock.Regression.ExponentiallyRare` and `OAI.SKRatioClock.Regression.standardArrayLaw` (definitions bundle `OAIQ024S001` of this split); `OAI.SKRatio.Planted.augmentedDisorder` and `OAI.SKRatio.Planted.reducedForm` (definitions bundle `OAIQ024S008` of this split); `OAI.SKRatio.coupling` (the published bundle `Def_SKRatio`).
--
--   **Used by.** The proof of `OAI.SKRatio.Planted.ratio_cutoff_of_scalar` of this split imports it.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Variational/ReducedForm.lean (declaration OAI.SKRatio.Planted.reduced_error_rare)

import Mathlib
import Definitions.Def_SKRatio
import Definitions.Def_OAIQ024S008

section

attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet Calculus Scalar
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem reduced_error_rare {β : ℝ} (hβ : 0<β) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n => {g | ∃ p : Fin n → ℝ, u*(∑ i, p i^2)<
        |gradientForm (coupling (augmentedDisorder β g)) p-reducedForm β g p|}) := by
  sorry

end SKRatio.Planted

end

end OAI
end
