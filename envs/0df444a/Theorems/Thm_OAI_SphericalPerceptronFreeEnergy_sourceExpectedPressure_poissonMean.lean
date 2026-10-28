-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_sourceExpectedPressure_poissonMean
-- name    : OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_poissonMean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:13:10.028107+00:00
-- url     : https://prove2.me/theorems/efb6bddd-4781-4df7-8722-f6a7a1d99132
-- title:
--   OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_poissonMean: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_poissonMean` of [lean/OAI/Probability/Perceptron/Variational/DensityDerivative.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/DensityDerivative.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   lemma sourceExpectedPressure_poissonMean (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
--       (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ)
--       (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
--       sourceExpectedPressure n k f p d h z t u =
--         (1/(n+1:ℕ))*poissonRealMean (sourceCountExpectedLog n k f p d h z u) ((n+1:ℕ)*(t:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.poissonRealMean` (definitions bundle `OAIQ61Pf001` of this split); `OAI.SphericalPerceptronFreeEnergy.sourceCountExpectedLog` and `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure` (definitions bundle `OAIQ61Pf002` of this split).
--
--   **Used by.** The proofs of `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_density_comparison`, `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_patternFree`, `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_pure_derivative`, `OAI.SphericalPerceptronFreeEnergy.source_global_contact_density` and `OAI.SphericalPerceptronFreeEnergy.source_zeroField_original_compare` of this split import it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/DensityDerivative.lean (declaration OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_poissonMean)

import Mathlib
import Definitions.Def_OAIQ61Pf002

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceExpectedPressure_poissonMean (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    sourceExpectedPressure n k f p d h z t u =
      (1/(n+1:ℕ))*poissonRealMean (sourceCountExpectedLog n k f p d h z u) ((n+1:ℕ)*(t:ℝ)) := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
