-- Prove2me | Theorems.Thm_OAI_SphericalPerceptron_finiteSphericalFieldValue_all_depths_uniform
-- name    : OAI.SphericalPerceptron.finiteSphericalFieldValue_all_depths_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T17:44:54.990368+00:00
-- url     : https://prove2.me/theorems/5b2668dc-563c-4001-893b-d844f6c0cf1c
-- title:
--   OAI.SphericalPerceptron.finiteSphericalFieldValue_all_depths_uniform: intermediate lemma from OpenAI, Perceptron free energies and microscopic jamming exponents (result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptron.spherical_linear_field_formula`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perceptron free energies and microscopic jamming exponents (result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptron.finiteSphericalFieldValue_all_depths_uniform` of [lean/OAI/Probability/SphericalField/Fields/DepthUniform.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SphericalField/Fields/DepthUniform.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptron`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators`):
--
--   ```lean
--   theorem finiteSphericalFieldValue_all_depths_uniform (H : ℝ) (hH : 0 ≤ H)
--       (ε : ℝ) (hε : 0 < ε) :
--       ∀ᶠ n : ℕ in atTop, ∀ (d : ℕ) (w h : Fin (d+1) → ℝ)
--         (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1),
--         Monotone h → 0 ≤ h 0 → h (Fin.last d) ≤ H →
--         |finiteSphericalFieldValue n d w h-
--           sInf (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)| < ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptron.finiteSphericalDualValues` and `OAI.SphericalPerceptron.finiteSphericalFieldValue` (the published bundle `Def_SphericalField`).
--
--   **Used by.** The proof of `OAI.SphericalPerceptron.spherical_linear_field_formula` of this split imports it.
-- source:
--   OpenAI, Perceptron free energies and microscopic jamming exponents (result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SphericalField.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SphericalField/Fields/DepthUniform.lean (declaration OAI.SphericalPerceptron.finiteSphericalFieldValue_all_depths_uniform)

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
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

theorem finiteSphericalFieldValue_all_depths_uniform (H : ℝ) (hH : 0 ≤ H)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (d : ℕ) (w h : Fin (d+1) → ℝ)
      (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1),
      Monotone h → 0 ≤ h 0 → h (Fin.last d) ≤ H →
      |finiteSphericalFieldValue n d w h-
        sInf (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)| < ε := by
  sorry

end SphericalPerceptron
end
end

end OAI
end
