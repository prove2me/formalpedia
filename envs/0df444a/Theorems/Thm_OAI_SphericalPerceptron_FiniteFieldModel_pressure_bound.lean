-- Prove2me | Theorems.Thm_OAI_SphericalPerceptron_FiniteFieldModel_pressure_bound
-- name    : OAI.SphericalPerceptron.FiniteFieldModel.pressure_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T17:45:42.852414+00:00
-- url     : https://prove2.me/theorems/6b0f7762-6e49-428d-97a8-dc204d1058a3
-- title:
--   OAI.SphericalPerceptron.FiniteFieldModel.pressure_bound: intermediate lemma from OpenAI, Perceptron free energies and microscopic jamming exponents (result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptron.spherical_linear_field_formula`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perceptron free energies and microscopic jamming exponents (result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptron.FiniteFieldModel.pressure_bound` of [lean/OAI/Probability/SphericalField/Fields/FiniteModels.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SphericalField/Fields/FiniteModels.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptron`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators`):
--
--   ```lean
--   lemma FiniteFieldModel.pressure_bound {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g)
--       {H : ℝ} (hH : 0 ≤ H) (hf : ∀ᵐ u ∂timeLaw, f u ∈ Icc (0:ℝ) H)
--       (hg : ∀ᵐ u ∂timeLaw, g u ∈ Icc (0:ℝ) H) (n : ℕ) :
--       |M.pressure n-N.pressure n| ≤ sphericalContinuityConstant n H*(∫ u, |f u-g u| ∂timeLaw)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptron.sphericalContinuityConstant` (definitions bundle `OAIB3Sp000` of this split); `OAI.SphericalPerceptron.FiniteFieldModel`, `OAI.SphericalPerceptron.Time`, `OAI.SphericalPerceptron.timeLaw` and `OAI.SphericalPerceptron.FiniteFieldModel.pressure` (the published bundle `Def_SphericalField`).
--
--   **Used by.** The proof of `OAI.SphericalPerceptron.spherical_linear_field_formula` of this split imports it.
-- source:
--   OpenAI, Perceptron free energies and microscopic jamming exponents (result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SphericalField.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SphericalField/Fields/FiniteModels.lean (declaration OAI.SphericalPerceptron.FiniteFieldModel.pressure_bound)

import Mathlib
import Definitions.Def_SphericalField
import Definitions.Def_OAIB3Sp000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

lemma FiniteFieldModel.pressure_bound {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g)
    {H : ℝ} (hH : 0 ≤ H) (hf : ∀ᵐ u ∂timeLaw, f u ∈ Icc (0:ℝ) H)
    (hg : ∀ᵐ u ∂timeLaw, g u ∈ Icc (0:ℝ) H) (n : ℕ) :
    |M.pressure n-N.pressure n| ≤ sphericalContinuityConstant n H*(∫ u, |f u-g u| ∂timeLaw) := by
  sorry

end SphericalPerceptron
end
end

end OAI
end
