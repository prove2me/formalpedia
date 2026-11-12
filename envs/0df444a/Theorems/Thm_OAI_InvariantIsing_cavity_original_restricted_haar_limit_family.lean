-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_original_restricted_haar_limit_family
-- name    : OAI.InvariantIsing.cavity_original_restricted_haar_limit_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:23:06.924206+00:00
-- url     : https://prove2.me/theorems/f88a427e-c427-47fd-8188-efedc7b003b2
-- title:
--   OAI.InvariantIsing.cavity_original_restricted_haar_limit_family: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_original_restricted_haar_limit_family` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityOriginalRestrictedFamily.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityOriginalRestrictedFamily.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter`, `open scoped Topology Matrix`):
--
--   ```lean
--   theorem cavity_original_restricted_haar_limit_family {m d n : ℕ}
--       (N depth : ℕ → ℕ) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
--       (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
--       (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
--       (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
--       (es : Fin (m*n) ≃ Fin (d+n))
--       (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
--       (hk : ∀ j a, d ≤ k j a)
--       (η : (j : ℕ) → Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
--       [∀ j, IsProbabilityMeasure (η j)]
--       (l w : ℕ → Fin m → ℕ)
--       (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
--       (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
--       (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
--       [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
--       (ν : (j : ℕ) → Measure (Orthogonal (N j)))
--       [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
--       (T : (j : ℕ) → LabeledTree (depth j)) (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
--       (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2) (t : ℝ)
--       {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
--       (F : (j : ℕ) → (Fin 2 → (Spin (N j) × LabeledLeaf (depth j)) × Spin n) → ℝ)
--       (hF : ∀ j σ, |F j σ| ≤ M) (A : CavityFactorBlocks d n)
--       (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
--         {U | δ < cavityFactorDeviation
--           (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
--             (cavityCompressionGrams (g j) U)) A}) atTop (𝓝 0)) :
--       let E := fun j => cavityBaseGroupEquiv (k j) (e j) a₀
--       let eig := fun j => diagonalPerturbedEigenvalues (fun i => lam ((E j).symm i).1)
--         (cavitySpectralGroup (fun i => ((E j).symm i).1)) (v j) t
--       let τ := cavityFactorSize (t • A.1) (t • A.2.1) (t • A.2.2) * (1+R^2)
--       Tendsto (fun j =>
--         (∫ U, cavityOriginalGeometricMean (g j) (cavityConcreteComplement es B₀) (T j)
--           (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) t)
--           (u j) (1+R^2) (fun σ => F j (fun i =>
--             (((σ i).1.1,(σ i).2),(σ i).1.2)))
--           (cavityOrientationLift (Nat.add_pos_left (hN j) n) U) ∂μ j) -
--         ∫ p, cavityWeightedReplicaMean ((cavityRotationProbability (eig j)
--             (cavitySpectralGroup (fun i => ((E j).symm i).1)) (u j) p.1).prod (uniformSpinPrior n))
--           (fun x => cavityHaarRestrictedWeight (fun i => (a₀ i,i))
--             (cavityRotationVectors (cavityBaseGroupDimension (k j) a₀) (E j))
--             (cavityCanonicalGroupFrame (k j) (e j) a₀ (hk j))
--             (t • A.1) (t • A.2.1) (t • A.2.2) τ R (p,x)) (F j)
--           ∂((((ν j).prod (Measure.dirac (T j))).prod gaussianCoordinates).prod (η j)))
--         atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` and `OAI.InvariantIsing.CavityFactorBlocks` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.cavityBaseGroupDimension`, `OAI.InvariantIsing.cavityBaseGroupEquiv`, `OAI.InvariantIsing.cavityCanonicalGroupFrame`, `OAI.InvariantIsing.cavityCompressionGrams`, `OAI.InvariantIsing.cavityConcreteComplement`, `OAI.InvariantIsing.cavityFactorSize`, `OAI.InvariantIsing.cavityOrientationLift`, `OAI.InvariantIsing.cavitySpectralGroup`, `OAI.InvariantIsing.cavityWeightedReplicaMean` and `OAI.InvariantIsing.diagonalPerturbedEigenvalues` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityCompressionFactorBlocks`, `OAI.InvariantIsing.cavityFactorDeviation`, `OAI.InvariantIsing.cavityHaarRestrictedWeight`, `OAI.InvariantIsing.cavityOriginalGeometricMean`, `OAI.InvariantIsing.cavityRotationProbability`, `OAI.InvariantIsing.cavityRotationVectors` and `OAI.InvariantIsing.uniformSpinPrior` (definitions bundle `OAIQ258003` of this split); `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.gaussianCoordinates`, `OAI.IsingPerceptron.labeledLeafMeasurableSpace` and `OAI.IsingPerceptron.labeledTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Orthogonal` and `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_original_overlap_limit` and `OAI.InvariantIsing.cavity_original_spin_limit` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityOriginalRestrictedFamily.lean (declaration OAI.InvariantIsing.cavity_original_restricted_haar_limit_family)

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
import Definitions.Def_OAIQ258003

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Matrix

namespace InvariantIsing

theorem cavity_original_restricted_haar_limit_family {m d n : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
    (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (η : (j : ℕ) → Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j, IsProbabilityMeasure (η j)]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (N j)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (T : (j : ℕ) → LabeledTree (depth j)) (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2) (t : ℝ)
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (F : (j : ℕ) → (Fin 2 → (Spin (N j) × LabeledLeaf (depth j)) × Spin n) → ℝ)
    (hF : ∀ j σ, |F j σ| ≤ M) (A : CavityFactorBlocks d n)
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A}) atTop (𝓝 0)) :
    let E := fun j => cavityBaseGroupEquiv (k j) (e j) a₀
    let eig := fun j => diagonalPerturbedEigenvalues (fun i => lam ((E j).symm i).1)
      (cavitySpectralGroup (fun i => ((E j).symm i).1)) (v j) t
    let τ := cavityFactorSize (t • A.1) (t • A.2.1) (t • A.2.2) * (1+R^2)
    Tendsto (fun j =>
      (∫ U, cavityOriginalGeometricMean (g j) (cavityConcreteComplement es B₀) (T j)
        (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) t)
        (u j) (1+R^2) (fun σ => F j (fun i =>
          (((σ i).1.1,(σ i).2),(σ i).1.2)))
        (cavityOrientationLift (Nat.add_pos_left (hN j) n) U) ∂μ j) -
      ∫ p, cavityWeightedReplicaMean ((cavityRotationProbability (eig j)
          (cavitySpectralGroup (fun i => ((E j).symm i).1)) (u j) p.1).prod (uniformSpinPrior n))
        (fun x => cavityHaarRestrictedWeight (fun i => (a₀ i,i))
          (cavityRotationVectors (cavityBaseGroupDimension (k j) a₀) (E j))
          (cavityCanonicalGroupFrame (k j) (e j) a₀ (hk j))
          (t • A.1) (t • A.2.1) (t • A.2.2) τ R (p,x)) (F j)
        ∂((((ν j).prod (Measure.dirac (T j))).prod gaussianCoordinates).prod (η j)))
      atTop (𝓝 0) := by
  sorry

end InvariantIsing

end

end OAI
end
