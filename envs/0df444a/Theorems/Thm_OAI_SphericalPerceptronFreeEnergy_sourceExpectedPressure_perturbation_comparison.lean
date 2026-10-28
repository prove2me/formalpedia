-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_sourceExpectedPressure_perturbation_comparison
-- name    : OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_perturbation_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:12:38.370751+00:00
-- url     : https://prove2.me/theorems/8fcf2dc7-1f61-4f20-84af-170a2a983771
-- title:
--   OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_perturbation_comparison: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_perturbation_comparison` of [lean/OAI/Probability/Perceptron/Interpolation/PerturbationComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Interpolation/PerturbationComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   lemma sourceExpectedPressure_perturbation_comparison (n k : ℕ) (f : ℝ →ᵇ ℝ)
--       (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
--       (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (z : Fin k → ℝ) (hz : StrictMono z)
--       (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0)
--       {u v : Fin (n+1) → ℝ} (hu : ∀ j, u j ∈ Icc 0 2) (hv : ∀ j, v j ∈ Icc 0 2) :
--       |(∫ a, sourceKernelPressure n k f p d v h a ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw))-
--         ∫ a, sourceKernelPressure n k f p d u h a ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw)| ≤
--         8*perturbationScale (n+1)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.IndexedCascadeBase`, `OAI.SphericalPerceptronFreeEnergy.SourceBaseData`, `OAI.SphericalPerceptronFreeEnergy.countableGaussianLaw`, `OAI.SphericalPerceptronFreeEnergy.perturbationScale` and `OAI.SphericalPerceptronFreeEnergy.sourceBaseDataLaw` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.sourceKernelPressure` (definitions bundle `OAIQ61Pf002` of this split).
--
--   **Used by.** The proofs of `OAI.SphericalPerceptronFreeEnergy.sourceNegativeContact_field_interior`, `OAI.SphericalPerceptronFreeEnergy.sourceNegativeContact_positive_density`, `OAI.SphericalPerceptronFreeEnergy.source_contact_monomial_tendsto` and `OAI.SphericalPerceptronFreeEnergy.source_zeroField_original_compare` of this split import it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Interpolation/PerturbationComparison.lean (declaration OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_perturbation_comparison)

import Mathlib
import Definitions.Def_OAIQ61Pf002

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceExpectedPressure_perturbation_comparison (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0)
    {u v : Fin (n+1) → ℝ} (hu : ∀ j, u j ∈ Icc 0 2) (hv : ∀ j, v j ∈ Icc 0 2) :
    |(∫ a, sourceKernelPressure n k f p d v h a ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw))-
      ∫ a, sourceKernelPressure n k f p d u h a ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw)| ≤
      8*perturbationScale (n+1)^2 := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
