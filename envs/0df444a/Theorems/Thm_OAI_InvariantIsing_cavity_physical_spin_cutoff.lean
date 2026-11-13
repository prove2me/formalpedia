-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_physical_spin_cutoff
-- name    : OAI.InvariantIsing.cavity_physical_spin_cutoff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:36:25.965781+00:00
-- url     : https://prove2.me/theorems/9e08a1e0-434d-41e9-bd99-a6ba96059a15
-- title:
--   OAI.InvariantIsing.cavity_physical_spin_cutoff: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_physical_spin_cutoff` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityPhysicalSpinCutoff.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityPhysicalSpinCutoff.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set`, `open scoped BigOperators Topology BoundedContinuousFunction`):
--
--   ```lean
--   theorem cavity_physical_spin_cutoff (hpub : PanchenkoTalagrandFieldPairInput)
--       {m q dim kspin : ℕ} (N depth : ℕ → ℕ) (hN : ∀ n, 0 < N n)
--       (dims : ℕ → Fin m → ℕ) (hgroups : ∀ n a, 0 < dims n a)
--       (hdims : ∀ a, Tendsto (fun n => dims n a) atTop atTop)
--       (E : (n : ℕ) → ((a : Fin m) × Fin (dims n a)) ≃ Fin (N n))
--       (μ : (n : ℕ) → Measure (Orthogonal (N n))) [∀ n, IsProbabilityMeasure (μ n)]
--       (θ : (n : ℕ) → Measure (LabeledTree (depth n))) [∀ n, IsProbabilityMeasure (θ n)]
--       (μG : (n : ℕ) → (a : Fin m) → Measure (Orthogonal (dims n a)))
--       [∀ n a, IsProbabilityMeasure (μG n a)] [∀ n a, (μG n a).IsMulRightInvariant]
--       (A₀ : (n : ℕ) → (a : Fin m) → Matrix (Fin (dims n a)) (Fin q) ℝ)
--       (hA₀ : ∀ n a, (A₀ n a).transpose * A₀ n a = 1)
--       (eigN : (n : ℕ) → Fin (N n) → ℝ) (u : ℕ → ℕ → ℝ)
--       {c : ℝ} (hc : 0 < c) (hcG : ∀ n a, c ≤ (dims n a : ℝ)/N n)
--       (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
--       (hρlim : Tendsto (fun n a => (dims n a : ℝ)/N n) atTop (𝓝 ρ))
--       (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
--       (hlim : Tendsto (fun n => cavityRotationArrayLaw (μ n) (θ n) (eigN n)
--         (cavitySpectralGroup (fun i => ((E n).symm i).1)) (u n)) atTop (𝓝 Q₀))
--       (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m + 1))))
--       (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralGram x)
--       (d : Fin (m + 1) → ℝ) (hd0 : ∀ j, 0 ≤ d j)
--       (hd : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ i j, (x (i,i) j : ℝ) = d j)
--       (hE : ∀ e : ℕ → ℕ, Function.Injective e →
--         (Q₀ : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q₀)
--       (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
--       (hn : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
--       (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
--         spectralOffWardResidual Q₀ ρ eig j l Φ = 0)
--       (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ eig j l = 0)
--       (g : Fin dim → Fin m) (e : Fin dim → Fin m × Fin q)
--       (he : Function.Injective e) (heg : ∀ j, (e j).1 = g j)
--       (hdim : 0 < dim) (hkspin : 0 < kspin)
--       (B₀ : Matrix (Fin (m*kspin)) (Fin dim) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
--       (hBE : B₀.transpose * cavityLimitingStack (n := kspin) ρ = 0)
--       (hcomplete : B₀ * B₀.transpose + cavityLimitingStack (n := kspin) ρ *
--         (cavityLimitingStack (n := kspin) ρ).transpose = 1)
--       (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
--       (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (site : Fin kspin)
--       {M : ℝ} (hΦb : ∀ x, |Φ x| ≤ M)
--       (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) (hblim : Tendsto b atTop atTop)
--       (hnull : ∀ j s, (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m s) : Measure
--         (SpectralBlock m s × EuclideanSpace ℝ (Fin m × (Fin s × Fin q))))
--         {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = b j} = 0) :
--       let p := spectralSpinQuantilePath Q₀ hP hn
--       let K := B₀.transpose * cavityRepeatedSpectrum (n := kspin) eig * B₀ -
--         Matrix.diagonal (fun i => eig (g i))
--       let L := B₀.transpose * cavityRepeatedSpectrum (n := kspin) eig *
--         cavityLimitingStack (n := kspin) ρ
--       let Cspin := (finiteR ρ eig hρ hρsum 0) • (1 : Matrix (Fin kspin) (Fin kspin) ℝ)
--       let τ := fun j => cavityFactorSize K L Cspin * (1+(b j)^2)
--       ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ n in atTop,
--         |(∫ ω, cavityWeightedReplicaMean
--             ((cavityRotationProbability (eigN n)
--               (cavitySpectralGroup (fun i => ((E n).symm i).1)) (u n) ω.1).prod
--               (uniformSpinPrior kspin))
--             (fun x => cavityHaarRestrictedWeight e (cavityRotationVectors (dims n) (E n))
--               (A₀ n) K L Cspin (τ j) (b j) (ω,x))
--             (fun σ : Fin 2 → (Spin (N n) × LabeledLeaf (depth n)) × Spin kspin =>
--               Φ (cavityTotalSpinOverlap ((σ 0).1.1,(σ 1).1.1)) *
--               (spinValue ((σ 0).2 site) * spinValue ((σ 1).2 site)))
--             ∂(((μ n).prod (θ n)).prod gaussianCoordinates).prod (Measure.pi (μG n))) -
--           ∫ t, Φ (cavityStrictUniformPath p n t) *
--             fieldMagnetizationPath (cavityStrictUniformField ρ eig hρ hρsum p n) t ∂pathMeasure| < ε
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpectralArray`, `OAI.InvariantIsing.SpectralBlock`, `OAI.InvariantIsing.SpectralEntry`, `OAI.InvariantIsing.SpectralGram`, `OAI.InvariantIsing.SpectralPartitionGeometry`, `OAI.InvariantIsing.cavityFactorSize`, `OAI.InvariantIsing.cavityLimitingStack`, `OAI.InvariantIsing.cavityRepeatedSpectrum`, `OAI.InvariantIsing.cavityReplicaRadius`, `OAI.InvariantIsing.cavitySelectedGroupProjection`, `OAI.InvariantIsing.cavitySpectralGroup`, `OAI.InvariantIsing.cavitySpectralGroupBlock`, `OAI.InvariantIsing.cavityWeightedReplicaMean` and `OAI.InvariantIsing.finiteR` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.PanchenkoTalagrandFieldPairInput`, `OAI.InvariantIsing.cavityBlockMarkedLaw`, `OAI.InvariantIsing.cavityHaarRestrictedWeight`, `OAI.InvariantIsing.cavityRotationArrayLaw`, `OAI.InvariantIsing.cavityRotationProbability`, `OAI.InvariantIsing.cavityRotationVectors`, `OAI.InvariantIsing.cavityStrictUniformField`, `OAI.InvariantIsing.cavityStrictUniformPath`, `OAI.InvariantIsing.cavityTotalSpinOverlap` and `OAI.InvariantIsing.uniformSpinPrior` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.permuteSpectralArray`, `OAI.InvariantIsing.spectralDiagonalWardResidual` and `OAI.InvariantIsing.spectralOffWardResidual` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.fieldMagnetizationPath` and `OAI.InvariantIsing.spectralSpinQuantilePath` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.HasEntryGhirlandaGuerra`, `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.gaussianCoordinates`, `OAI.IsingPerceptron.labeledLeafMeasurableSpace` and `OAI.IsingPerceptron.labeledTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Orthogonal`, `OAI.InvariantIsing.OverlapPath`, `OAI.InvariantIsing.Spin`, `OAI.InvariantIsing.pathMeasure` and `OAI.InvariantIsing.spinValue` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.cavity_original_spin_limit` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityPhysicalSpinCutoff.lean (declaration OAI.InvariantIsing.cavity_physical_spin_cutoff)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_physical_spin_cutoff (hpub : PanchenkoTalagrandFieldPairInput)
    {m q dim kspin : ℕ} (N depth : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (dims : ℕ → Fin m → ℕ) (hgroups : ∀ n a, 0 < dims n a)
    (hdims : ∀ a, Tendsto (fun n => dims n a) atTop atTop)
    (E : (n : ℕ) → ((a : Fin m) × Fin (dims n a)) ≃ Fin (N n))
    (μ : (n : ℕ) → Measure (Orthogonal (N n))) [∀ n, IsProbabilityMeasure (μ n)]
    (θ : (n : ℕ) → Measure (LabeledTree (depth n))) [∀ n, IsProbabilityMeasure (θ n)]
    (μG : (n : ℕ) → (a : Fin m) → Measure (Orthogonal (dims n a)))
    [∀ n a, IsProbabilityMeasure (μG n a)] [∀ n a, (μG n a).IsMulRightInvariant]
    (A₀ : (n : ℕ) → (a : Fin m) → Matrix (Fin (dims n a)) (Fin q) ℝ)
    (hA₀ : ∀ n a, (A₀ n a).transpose * A₀ n a = 1)
    (eigN : (n : ℕ) → Fin (N n) → ℝ) (u : ℕ → ℕ → ℝ)
    {c : ℝ} (hc : 0 < c) (hcG : ∀ n a, c ≤ (dims n a : ℝ)/N n)
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρlim : Tendsto (fun n a => (dims n a : ℝ)/N n) atTop (𝓝 ρ))
    (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
    (hlim : Tendsto (fun n => cavityRotationArrayLaw (μ n) (θ n) (eigN n)
      (cavitySpectralGroup (fun i => ((E n).symm i).1)) (u n)) atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralGram x)
    (d : Fin (m + 1) → ℝ) (hd0 : ∀ j, 0 ≤ d j)
    (hd : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ i j, (x (i,i) j : ℝ) = d j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m + 1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
      spectralOffWardResidual Q₀ ρ eig j l Φ = 0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ eig j l = 0)
    (g : Fin dim → Fin m) (e : Fin dim → Fin m × Fin q)
    (he : Function.Injective e) (heg : ∀ j, (e j).1 = g j)
    (hdim : 0 < dim) (hkspin : 0 < kspin)
    (B₀ : Matrix (Fin (m*kspin)) (Fin dim) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (hBE : B₀.transpose * cavityLimitingStack (n := kspin) ρ = 0)
    (hcomplete : B₀ * B₀.transpose + cavityLimitingStack (n := kspin) ρ *
      (cavityLimitingStack (n := kspin) ρ).transpose = 1)
    (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (site : Fin kspin)
    {M : ℝ} (hΦb : ∀ x, |Φ x| ≤ M)
    (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) (hblim : Tendsto b atTop atTop)
    (hnull : ∀ j s, (cavityBlockMarkedLaw (q := q) Q₀ ρ (cavitySpectralGroupBlock m s) : Measure
      (SpectralBlock m s × EuclideanSpace ℝ (Fin m × (Fin s × Fin q))))
      {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = b j} = 0) :
    let p := spectralSpinQuantilePath Q₀ hP hn
    let K := B₀.transpose * cavityRepeatedSpectrum (n := kspin) eig * B₀ -
      Matrix.diagonal (fun i => eig (g i))
    let L := B₀.transpose * cavityRepeatedSpectrum (n := kspin) eig *
      cavityLimitingStack (n := kspin) ρ
    let Cspin := (finiteR ρ eig hρ hρsum 0) • (1 : Matrix (Fin kspin) (Fin kspin) ℝ)
    let τ := fun j => cavityFactorSize K L Cspin * (1+(b j)^2)
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ n in atTop,
      |(∫ ω, cavityWeightedReplicaMean
          ((cavityRotationProbability (eigN n)
            (cavitySpectralGroup (fun i => ((E n).symm i).1)) (u n) ω.1).prod
            (uniformSpinPrior kspin))
          (fun x => cavityHaarRestrictedWeight e (cavityRotationVectors (dims n) (E n))
            (A₀ n) K L Cspin (τ j) (b j) (ω,x))
          (fun σ : Fin 2 → (Spin (N n) × LabeledLeaf (depth n)) × Spin kspin =>
            Φ (cavityTotalSpinOverlap ((σ 0).1.1,(σ 1).1.1)) *
            (spinValue ((σ 0).2 site) * spinValue ((σ 1).2 site)))
          ∂(((μ n).prod (θ n)).prod gaussianCoordinates).prod (Measure.pi (μG n))) -
        ∫ t, Φ (cavityStrictUniformPath p n t) *
          fieldMagnetizationPath (cavityStrictUniformField ρ eig hρ hρsum p n) t ∂pathMeasure| < ε := by
  sorry

end InvariantIsing

end

end OAI
end
