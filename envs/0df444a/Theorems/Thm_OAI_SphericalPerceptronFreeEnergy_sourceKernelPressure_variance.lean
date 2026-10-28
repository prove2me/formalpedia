-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_sourceKernelPressure_variance
-- name    : OAI.SphericalPerceptronFreeEnergy.sourceKernelPressure_variance
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:13:41.490675+00:00
-- url     : https://prove2.me/theorems/26508d76-f265-46e7-8604-728a9f0a1002
-- title:
--   OAI.SphericalPerceptronFreeEnergy.sourceKernelPressure_variance: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.sourceKernelPressure_variance` of [lean/OAI/Probability/Perceptron/Variational/CouplingKernel.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/CouplingKernel.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   lemma sourceKernelPressure_variance (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
--       (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hz : StrictMono z)
--       (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (hu : ∀ j, u j ∈ Icc 1 2)
--       {H T : ℝ} (hH : 0 ≤ H) (hh : h 0 ≤ H) (t : ℝ≥0) (ht : (t:ℝ) ≤ T) :
--       variance (sourceKernelPressure n k f p d u h) ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) ≤
--         enrichedVarianceConstant k z f H T/(n+1:ℕ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.IndexedCascadeBase`, `OAI.SphericalPerceptronFreeEnergy.SourceBaseData`, `OAI.SphericalPerceptronFreeEnergy.countableGaussianLaw`, `OAI.SphericalPerceptronFreeEnergy.enrichedVarianceConstant` and `OAI.SphericalPerceptronFreeEnergy.sourceBaseDataLaw` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.sourceKernelPressure` (definitions bundle `OAIQ61Pf002` of this split).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.source_contact_joint_gg_rate` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/CouplingKernel.lean (declaration OAI.SphericalPerceptronFreeEnergy.sourceKernelPressure_variance)

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
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma sourceKernelPressure_variance (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (hu : ∀ j, u j ∈ Icc 1 2)
    {H T : ℝ} (hH : 0 ≤ H) (hh : h 0 ≤ H) (t : ℝ≥0) (ht : (t:ℝ) ≤ T) :
    variance (sourceKernelPressure n k f p d u h) ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) ≤
      enrichedVarianceConstant k z f H T/(n+1:ℕ) := by
  sorry

end SphericalPerceptronFreeEnergy

end

end OAI
end
