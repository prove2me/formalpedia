-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_sourceExpectedPressure_pure_derivative
-- name    : OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_pure_derivative
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:13:38.230989+00:00
-- url     : https://prove2.me/theorems/119cc4bc-2f82-427d-82aa-a8407a98a364
-- title:
--   OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_pure_derivative: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_pure_derivative` of [lean/OAI/Probability/Perceptron/Variational/LabelResponse.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/LabelResponse.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   lemma sourceExpectedPressure_pure_derivative (n k : ℕ) (f : ℝ →ᵇ ℝ)
--       (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ)
--       (j : Fin (n+1)) (hp : p j=0)
--       (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
--       HasDerivAt (fun r => sourceExpectedPressure n k f p d h z t (u+Pi.single j r))
--         ((1/(n+1:ℕ))*perturbationAmplitude (n+1) (fun _ => 1) j*
--           perturbationAmplitude (n+1) u j*pureLabelResponse p d j hp k h z) 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.perturbationAmplitude` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.pureLabelResponse` and `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure` (definitions bundle `OAIQ61Pf002` of this split).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.source_array_limit_label_law` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/LabelResponse.lean (declaration OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_pure_derivative)

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

lemma sourceExpectedPressure_pure_derivative (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ)
    (j : Fin (n+1)) (hp : p j=0)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    HasDerivAt (fun r => sourceExpectedPressure n k f p d h z t (u+Pi.single j r))
      ((1/(n+1:ℕ))*perturbationAmplitude (n+1) (fun _ => 1) j*
        perturbationAmplitude (n+1) u j*pureLabelResponse p d j hp k h z) 0 := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
