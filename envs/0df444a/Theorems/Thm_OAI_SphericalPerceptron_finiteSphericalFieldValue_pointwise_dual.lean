-- Prove2me | Theorems.Thm_OAI_SphericalPerceptron_finiteSphericalFieldValue_pointwise_dual
-- name    : OAI.SphericalPerceptron.finiteSphericalFieldValue_pointwise_dual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T17:44:55.660515+00:00
-- url     : https://prove2.me/theorems/fba84671-0fbc-429e-b774-f86f9fb1025b
-- title:
--   OAI.SphericalPerceptron.finiteSphericalFieldValue_pointwise_dual: intermediate lemma from OpenAI, Perceptron free energies and microscopic jamming exponents (result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptron.spherical_linear_field_formula`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perceptron free energies and microscopic jamming exponents (result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptron.finiteSphericalFieldValue_pointwise_dual` of [lean/OAI/Probability/SphericalField/Entropy/StationaryExistence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SphericalField/Entropy/StationaryExistence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptron`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   theorem finiteSphericalFieldValue_pointwise_dual {k : ℕ} (w h : Fin (k+1) → ℝ)
--       (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0 ≤ h 0) :
--       ∃ q : Fin (k+1) → Time, Monotone q ∧ (q (Fin.last k):ℝ) < 1 ∧
--         IsLeast (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)
--           (finiteSphericalDualObjective w h (fun i => (hw i).le) hw1 q) ∧
--         Tendsto (fun n : ℕ => finiteSphericalFieldValue n k w h) atTop
--           (𝓝 (sInf (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptron.Time`, `OAI.SphericalPerceptron.finiteSphericalDualObjective`, `OAI.SphericalPerceptron.finiteSphericalDualValues` and `OAI.SphericalPerceptron.finiteSphericalFieldValue` (the published bundle `Def_SphericalField`).
--
--   **Used by.** The proofs of `OAI.SphericalPerceptron.finiteSphericalFieldValue_tendsto_dual` and `OAI.SphericalPerceptron.spherical_linear_field_formula` of this split import it.
-- source:
--   OpenAI, Perceptron free energies and microscopic jamming exponents (result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SphericalField.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SphericalField/Entropy/StationaryExistence.lean (declaration OAI.SphericalPerceptron.finiteSphericalFieldValue_pointwise_dual)

import Mathlib
import Definitions.Def_SphericalField

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

theorem finiteSphericalFieldValue_pointwise_dual {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0 ≤ h 0) :
    ∃ q : Fin (k+1) → Time, Monotone q ∧ (q (Fin.last k):ℝ) < 1 ∧
      IsLeast (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)
        (finiteSphericalDualObjective w h (fun i => (hw i).le) hw1 q) ∧
      Tendsto (fun n : ℕ => finiteSphericalFieldValue n k w h) atTop
        (𝓝 (sInf (finiteSphericalDualValues w h (fun i => (hw i).le) hw1))) := by
  sorry

end SphericalPerceptron
end
end

end OAI
end
