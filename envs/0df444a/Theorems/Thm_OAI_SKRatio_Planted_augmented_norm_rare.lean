-- Prove2me | Theorems.Thm_OAI_SKRatio_Planted_augmented_norm_rare
-- name    : OAI.SKRatio.Planted.augmented_norm_rare
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:26:49.146708+00:00
-- url     : https://prove2.me/theorems/8c747c16-5697-4379-9d5a-ec30eb23fecd
-- title:
--   OAI.SKRatio.Planted.augmented_norm_rare: intermediate lemma from OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKRatio.Planted.augmented_norm_rare` of [lean/OAI/Probability/SKRatio/Matrices/AugmentedBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Matrices/AugmentedBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKRatio.Planted`, with `open scoped BigOperators NNReal ENNReal Topology`, `open MeasureTheory ProbabilityTheory Filter Set Real`, `open SKRatioClock.Regression MatrixNet Calculus`):
--
--   ```lean
--   lemma augmented_norm_rare {β δ : ℝ} (hβ : 0<β) (hδ : 0<δ) :
--       ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
--         (fun n => {g | 2*β+β^2+δ<euclideanOpNorm (coupling (augmentedDisorder (n := n) β g))})
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKRatio.Calculus.euclideanOpNorm` (definitions bundle `OAIQ024S000` of this split); `OAI.SKRatioClock.Regression.ExponentiallyRare` and `OAI.SKRatioClock.Regression.standardArrayLaw` (definitions bundle `OAIQ024S001` of this split); `OAI.SKRatio.Planted.augmentedDisorder` (definitions bundle `OAIQ024S008` of this split); `OAI.SKRatio.coupling` (the published bundle `Def_SKRatio`).
--
--   **Used by.** The proofs of `OAI.SKRatio.Planted.reduced_error_rare` and `OAI.SKRatio.Planted.residual_norm_rare` of this split import it.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Matrices/AugmentedBounds.lean (declaration OAI.SKRatio.Planted.augmented_norm_rare)

import Mathlib
import Definitions.Def_SKRatio
import Definitions.Def_OAIQ024S008

section

attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma augmented_norm_rare {β δ : ℝ} (hβ : 0<β) (hδ : 0<δ) :
    ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n => {g | 2*β+β^2+δ<euclideanOpNorm (coupling (augmentedDisorder (n := n) β g))}) := by
  sorry

end SKRatio.Planted

end

end OAI
end
