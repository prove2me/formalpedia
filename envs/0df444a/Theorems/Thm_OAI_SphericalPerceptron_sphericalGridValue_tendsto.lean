-- Prove2me | Theorems.Thm_OAI_SphericalPerceptron_sphericalGridValue_tendsto
-- name    : OAI.SphericalPerceptron.sphericalGridValue_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T17:45:52.816362+00:00
-- url     : https://prove2.me/theorems/bfd7fb4e-a369-4f41-99d3-3b21751eff8a
-- title:
--   OAI.SphericalPerceptron.sphericalGridValue_tendsto: intermediate lemma from OpenAI, Perceptron free energies and microscopic jamming exponents (result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptron.spherical_linear_field_formula`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perceptron free energies and microscopic jamming exponents (result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptron.sphericalGridValue_tendsto` of [lean/OAI/Probability/SphericalField/Fields/DepthUniform.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SphericalField/Fields/DepthUniform.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptron`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators`):
--
--   ```lean
--   lemma sphericalGridValue_tendsto (k : ℕ) (v : Fin (k+2) → ℝ) (hv : ∀ i, 0 ≤ v i) :
--       Tendsto (fun n => sphericalGridValue n k v) atTop (𝓝 (sphericalGridDual k v))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptron.sphericalGridDual` and `OAI.SphericalPerceptron.sphericalGridValue` (definitions bundle `OAIB3Sp000` of this split).
--
--   **Used by.** The proof of `OAI.SphericalPerceptron.finiteSphericalFieldValue_all_depths_uniform` of this split imports it.
-- source:
--   OpenAI, Perceptron free energies and microscopic jamming exponents (result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SphericalField.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SphericalField/Fields/DepthUniform.lean (declaration OAI.SphericalPerceptron.sphericalGridValue_tendsto)

import Mathlib
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

lemma sphericalGridValue_tendsto (k : ℕ) (v : Fin (k+2) → ℝ) (hv : ∀ i, 0 ≤ v i) :
    Tendsto (fun n => sphericalGridValue n k v) atTop (𝓝 (sphericalGridDual k v)) := by
  sorry

end SphericalPerceptron
end
end

end OAI
end
