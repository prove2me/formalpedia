-- Prove2me | Theorems.Thm_OAI_InvariantIsing_spinPriorPerturbation_arrayResidual_bound
-- name    : OAI.InvariantIsing.spinPriorPerturbation_arrayResidual_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:44:25.830203+00:00
-- url     : https://prove2.me/theorems/673188c7-8c90-4969-93b9-0e000f770d56
-- title:
--   OAI.InvariantIsing.spinPriorPerturbation_arrayResidual_bound: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.spinPriorPerturbation_arrayResidual_bound` of [lean/OAI/Probability/InvariantIsing/Fields/SpinPriorArrayResidualBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/SpinPriorArrayResidualBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem spinPriorPerturbation_arrayResidual_bound (hhaar : HaarConcentrationInput)
--       (hgauss : GaussianLipschitzVarianceInput) :
--       ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 3≤N →
--       ∀ μ : Measure (SpecialOrthogonal N), ∀ [IsProbabilityMeasure μ], μ.IsMulLeftInvariant →
--       ∀ m n : ℕ, ∀ π : Measure (Spin N), ∀ [IsProbabilityMeasure π],
--       ∀ b : ℕ → ℝ, CascadeExponents n b →
--       ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0<K → (∀ i, |eig i|≤K) →
--       ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, u j∈Set.Icc (1 : ℝ) 2) →
--       ∀ v : Fin m → ℝ, (∀ a, v a∈Set.Icc (1 : ℝ) 2) → ∀ t : ℝ, |t|≤1 →
--       ∀ h : ℕ → ℝ, Monotone h → 0≤h 0 → ∀ H : ℝ, h n≤H →
--         let d := fun j : Fin N => enumeratedSpectralDegree m j
--         let r := fun j : Fin N => enumeratedTreeDegree m j
--         let L := 4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2
--           ∂(rawCascadeLaw n b : Measure (RawTree n)))+H+4+C*(K+4*m+8)^2
--         perturbationScale N≤1/32 → contactStep N≤1/4 →
--         (∀ u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
--           spinPriorPerturbationObjective (n := n) μ π eig c I b t h u v≤ spinPriorPerturbationObjective (n := n) μ π eig c I b t h u' v') →
--         ∀ j : Fin N, ∀ q : ℕ, ∀ i : Fin (q+1),
--         ∀ D : SpectralBlock (m+1) (q+1) → ℝ, Continuous D →
--         ∀ B : ℝ, 0≤B → (∀ x, |D x|≤B) →
--         |spectralMonomialResidual
--           (spinPriorArrayLaw μ π (diagonalPerturbedEigenvalues eig I v t) c I d
--             (tensorPerturbationAmplitude N u) n b r h)
--           (q+1) i D (Fin.lastCases (r j) (d j))|≤tensorContactGGRate N j m L B
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.GaussianLipschitzVarianceInput`, `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.SpectralArray`, `OAI.InvariantIsing.SpectralBlock`, `OAI.InvariantIsing.SpectralEntry`, `OAI.InvariantIsing.diagonalPerturbedEigenvalues`, `OAI.InvariantIsing.enumeratedSpectralDegree`, `OAI.InvariantIsing.enumeratedTreeDegree` and `OAI.InvariantIsing.tensorPerturbationAmplitude` (definitions bundle `OAIQ258001` of this split); `OAI.IsingPerceptron.contactStep` (definitions bundle `OAIQ258002` of this split); `OAI.InvariantIsing.HaarConcentrationInput` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.spectralMonomialResidual` and `OAI.InvariantIsing.tensorContactGGRate` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.spinPriorArrayLaw` and `OAI.InvariantIsing.spinPriorPerturbationObjective` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.RawTree`, `OAI.IsingPerceptron.perturbationScale`, `OAI.IsingPerceptron.rawCascadeLaw`, `OAI.IsingPerceptron.rawTreeMeasurableSpace` and `OAI.IsingPerceptron.rawTreeTotal` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.spinPriorRestrictedContact_entropy_limit` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/SpinPriorArrayResidualBound.lean (declaration OAI.InvariantIsing.spinPriorPerturbation_arrayResidual_bound)

import Mathlib
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology
namespace InvariantIsing

theorem spinPriorPerturbation_arrayResidual_bound (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 3≤N →
    ∀ μ : Measure (SpecialOrthogonal N), ∀ [IsProbabilityMeasure μ], μ.IsMulLeftInvariant →
    ∀ m n : ℕ, ∀ π : Measure (Spin N), ∀ [IsProbabilityMeasure π],
    ∀ b : ℕ → ℝ, CascadeExponents n b →
    ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0<K → (∀ i, |eig i|≤K) →
    ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, u j∈Set.Icc (1 : ℝ) 2) →
    ∀ v : Fin m → ℝ, (∀ a, v a∈Set.Icc (1 : ℝ) 2) → ∀ t : ℝ, |t|≤1 →
    ∀ h : ℕ → ℝ, Monotone h → 0≤h 0 → ∀ H : ℝ, h n≤H →
      let d := fun j : Fin N => enumeratedSpectralDegree m j
      let r := fun j : Fin N => enumeratedTreeDegree m j
      let L := 4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2
        ∂(rawCascadeLaw n b : Measure (RawTree n)))+H+4+C*(K+4*m+8)^2
      perturbationScale N≤1/32 → contactStep N≤1/4 →
      (∀ u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
        spinPriorPerturbationObjective (n := n) μ π eig c I b t h u v≤ spinPriorPerturbationObjective (n := n) μ π eig c I b t h u' v') →
      ∀ j : Fin N, ∀ q : ℕ, ∀ i : Fin (q+1),
      ∀ D : SpectralBlock (m+1) (q+1) → ℝ, Continuous D →
      ∀ B : ℝ, 0≤B → (∀ x, |D x|≤B) →
      |spectralMonomialResidual
        (spinPriorArrayLaw μ π (diagonalPerturbedEigenvalues eig I v t) c I d
          (tensorPerturbationAmplitude N u) n b r h)
        (q+1) i D (Fin.lastCases (r j) (d j))|≤tensorContactGGRate N j m L B := by
  sorry

end InvariantIsing

end

end OAI
end
