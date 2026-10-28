-- Prove2me | Theorems.Thm_OAI_SphericalPerceptron_sphericalGridValue_compact_uniform
-- name    : OAI.SphericalPerceptron.sphericalGridValue_compact_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T17:45:54.549356+00:00
-- url     : https://prove2.me/theorems/a44844db-73b3-45a7-8449-8d3f0e63d2cf
-- title:
--   OAI.SphericalPerceptron.sphericalGridValue_compact_uniform: intermediate lemma from OpenAI, Perceptron free energies and microscopic jamming exponents (result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptron.spherical_linear_field_formula`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perceptron free energies and microscopic jamming exponents (result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptron.sphericalGridValue_compact_uniform` of [lean/OAI/Probability/SphericalField/Fields/UniformGrid.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SphericalField/Fields/UniformGrid.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptron`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators`):
--
--   ```lean
--   lemma sphericalGridValue_compact_uniform (k : ℕ) (H : ℝ) :
--       TendstoUniformlyOn (fun n => sphericalGridValue n k) (sphericalGridDual k) atTop
--         (Icc (fun _ => 0) (fun _ => H))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptron.sphericalGridDual` and `OAI.SphericalPerceptron.sphericalGridValue` (definitions bundle `OAIB3Sp000` of this split).
--
--   **Used by.** The proofs of `OAI.SphericalPerceptron.finiteSphericalFieldValue_all_depths_uniform` and `OAI.SphericalPerceptron.sphericalGridValue_tendsto` of this split import it.
-- source:
--   OpenAI, Perceptron free energies and microscopic jamming exponents (result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SphericalField.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SphericalField/Fields/UniformGrid.lean (declaration OAI.SphericalPerceptron.sphericalGridValue_compact_uniform)

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

lemma sphericalGridValue_compact_uniform (k : ℕ) (H : ℝ) :
    TendstoUniformlyOn (fun n => sphericalGridValue n k) (sphericalGridDual k) atTop
      (Icc (fun _ => 0) (fun _ => H)) := by
  sorry

end SphericalPerceptron
end
end

end OAI
end
