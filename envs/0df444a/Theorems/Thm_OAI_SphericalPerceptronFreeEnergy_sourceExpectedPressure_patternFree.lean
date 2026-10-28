-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_sourceExpectedPressure_patternFree
-- name    : OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_patternFree
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:12:52.700284+00:00
-- url     : https://prove2.me/theorems/27925642-ccd9-471e-8c40-713f6732303f
-- title:
--   OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_patternFree: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_patternFree` of [lean/OAI/Probability/Perceptron/Pressure/PatternFree.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Pressure/PatternFree.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   lemma sourceExpectedPressure_patternFree (n k : ℕ) (f : ℝ →ᵇ ℝ)
--       (p d : Fin (n+1)→ℕ) (w h : Fin (k+1)→ℝ)
--       (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0≤h 0) :
--       sourceExpectedPressure n k f p d h (stepCumulative w) 0 (fun _ => 0)=
--         finiteSphericalFieldValue n k w h
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.finiteSphericalFieldValue` and `OAI.SphericalPerceptronFreeEnergy.stepCumulative` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure` (definitions bundle `OAIQ61Pf002` of this split).
--
--   **Used by.** The proofs of `OAI.SphericalPerceptronFreeEnergy.sourceNegativeContact_field_interior` and `OAI.SphericalPerceptronFreeEnergy.sourceNegativeContact_positive_density` of this split import it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Pressure/PatternFree.lean (declaration OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_patternFree)

import Mathlib
import Definitions.Def_OAIQ61Pf002

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceExpectedPressure_patternFree (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (w h : Fin (k+1)→ℝ)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0≤h 0) :
    sourceExpectedPressure n k f p d h (stepCumulative w) 0 (fun _ => 0)=
      finiteSphericalFieldValue n k w h := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
