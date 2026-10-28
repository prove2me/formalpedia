-- Prove2me | Theorems.Thm_OAI_SphericalPerceptron_finiteAmplitudeSphereValue_tendsto
-- name    : OAI.SphericalPerceptron.finiteAmplitudeSphereValue_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T17:45:51.056907+00:00
-- url     : https://prove2.me/theorems/f3614a92-a878-4ff2-b9d6-2354aeb5036c
-- title:
--   OAI.SphericalPerceptron.finiteAmplitudeSphereValue_tendsto: intermediate lemma from OpenAI, Perceptron free energies and microscopic jamming exponents (result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptron.spherical_linear_field_formula`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perceptron free energies and microscopic jamming exponents (result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptron.finiteAmplitudeSphereValue_tendsto` of [lean/OAI/Probability/SphericalField/Sphere/AmplitudeLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SphericalField/Sphere/AmplitudeLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptron`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   lemma finiteAmplitudeSphereValue_tendsto {k : ℕ} (w : Fin (k+1) → ℝ)
--       (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (a : Fin (k+1) → ℝ) :
--       Tendsto (fun n : ℕ => finiteAmplitudeSphereValue n k w a) atTop
--         (𝓝 (finiteAmplitudeSphereDual w (fun i => (hw i).le) hw1 a))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptron.finiteAmplitudeSphereDual` and `OAI.SphericalPerceptron.finiteAmplitudeSphereValue` (definitions bundle `OAIB3Sp000` of this split).
--
--   **Used by.** The proofs of `OAI.SphericalPerceptron.sphericalGridValue_compact_uniform` and `OAI.SphericalPerceptron.spherical_linear_field_formula` of this split import it.
-- source:
--   OpenAI, Perceptron free energies and microscopic jamming exponents (result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SphericalField.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SphericalField/Sphere/AmplitudeLimit.lean (declaration OAI.SphericalPerceptron.finiteAmplitudeSphereValue_tendsto)

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
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

lemma finiteAmplitudeSphereValue_tendsto {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (a : Fin (k+1) → ℝ) :
    Tendsto (fun n : ℕ => finiteAmplitudeSphereValue n k w a) atTop
      (𝓝 (finiteAmplitudeSphereDual w (fun i => (hw i).le) hw1 a)) := by
  sorry

end SphericalPerceptron
end
end

end OAI
end
