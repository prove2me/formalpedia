-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_sourceLabelFreshLog_value
-- name    : OAI.SphericalPerceptronFreeEnergy.sourceLabelFreshLog_value
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:13:42.958066+00:00
-- url     : https://prove2.me/theorems/f622d1b0-406b-4b71-82bc-f271731d4b65
-- title:
--   OAI.SphericalPerceptronFreeEnergy.sourceLabelFreshLog_value: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.sourceLabelFreshLog_value` of [lean/OAI/Probability/Perceptron/Variational/LabelValue.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/LabelValue.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal NNReal BoundedContinuousFunction`):
--
--   ```lean
--   theorem sourceLabelFreshLog_value (n k : ℕ) (f : ℝ →ᵇ ℝ)
--       (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
--       (u : Fin (n+1)→ℝ) (z : Fin k→ℝ)
--       (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
--       (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1) (g : Jet3) (t : ℝ≥0) :
--       sourceLabelFreshLog n k q hq1 f g.f p d h u z t=labelProfileValue k z q hq1 g
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.Jet3` and `OAI.SphericalPerceptronFreeEnergy.labelProfileValue` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.sourceLabelFreshLog` (definitions bundle `OAIQ61Pf002` of this split).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.labelProfile_reference_full_exists` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/LabelValue.lean (declaration OAI.SphericalPerceptronFreeEnergy.sourceLabelFreshLog_value)

import Mathlib
import Definitions.Def_OAIQ61Pf002

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

theorem sourceLabelFreshLog_value (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1) (g : Jet3) (t : ℝ≥0) :
    sourceLabelFreshLog n k q hq1 f g.f p d h u z t=labelProfileValue k z q hq1 g := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
