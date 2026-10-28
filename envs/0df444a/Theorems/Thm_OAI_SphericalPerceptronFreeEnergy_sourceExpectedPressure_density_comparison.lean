-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_sourceExpectedPressure_density_comparison
-- name    : OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_density_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:12:17.555314+00:00
-- url     : https://prove2.me/theorems/1d81fb9b-32f5-462e-8dac-bfe5ba7d23b1
-- title:
--   OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_density_comparison: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_density_comparison` of [lean/OAI/Probability/Perceptron/Variational/DensityLipschitz.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/DensityLipschitz.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   lemma sourceExpectedPressure_density_comparison (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
--       (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ)
--       (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (s t : ℝ≥0) :
--       |sourceExpectedPressure n k f p d h z t u-sourceExpectedPressure n k f p d h z s u|≤
--         ‖f‖*|(t:ℝ)-(s:ℝ)|
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure` (definitions bundle `OAIQ61Pf002` of this split).
--
--   **Used by.** The proofs of `OAI.SphericalPerceptronFreeEnergy.sourceNegativeContact_field_interior` and `OAI.SphericalPerceptronFreeEnergy.source_global_contact_exists` of this split import it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/DensityLipschitz.lean (declaration OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_density_comparison)

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

lemma sourceExpectedPressure_density_comparison (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (s t : ℝ≥0) :
    |sourceExpectedPressure n k f p d h z t u-sourceExpectedPressure n k f p d h z s u|≤
      ‖f‖*|(t:ℝ)-(s:ℝ)| := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
