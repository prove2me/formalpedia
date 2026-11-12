-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_rooted_depth_test_transport
-- name    : OAI.InvariantIsing.cavity_rooted_depth_test_transport
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:23:46.966572+00:00
-- url     : https://prove2.me/theorems/d97833dc-7fce-45a6-9974-881dd3b003a6
-- title:
--   OAI.InvariantIsing.cavity_rooted_depth_test_transport: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_rooted_depth_test_transport` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityRootedDepthTransport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityRootedDepthTransport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped Matrix MatrixOrder Matrix.Norms.L2Operator`):
--
--   ```lean
--   theorem cavity_rooted_depth_test_transport {d k : ℕ} (n : ℕ)
--       (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
--       (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
--       (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
--       (hbCascade : CascadeExponents n b)
--       (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
--       (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
--       (hdet : ∀ i, IsUnit (1 - H i * K).det)
--       (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
--       (hQ : ∀ i, (cavityFactorPrecision
--         (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
--       (hR : (H n).PosSemidef)
--       (hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
--       (π : Measure (Spin k)) [IsProbabilityMeasure π] (a : ℕ → ℝ) :
--       let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
--         (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
--       let J₀ := (1 - H 0 * K)⁻¹
--       let P' := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (J₀ * S₀ * J₀.transpose)).prod
--         (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b
--           (cavityGaussianMarks (fun i =>
--             (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose)) : Measure _)
--       (∫ σ, cavityRootedDepthTest a σ
--         ∂((probabilityReplicaKernel (cavityRootedFullGibbs n K (H n) L C π)
--           (cavityRootedFullGibbs n K (H n) L C π).measurable) ∘ₘ P)) =
--       ∫ σ, cavityRootedDepthTest a σ
--         ∂((probabilityReplicaKernel (cavityRootedFullGibbs n 0 (cavityResolvent K (H n)) L C π)
--           (cavityRootedFullGibbs n 0 (cavityResolvent K (H n)) L C π).measurable) ∘ₘ P')
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.cavityBackwardQuadratic`, `OAI.InvariantIsing.cavityFactorPrecision`, `OAI.InvariantIsing.cavityGaussianMarks` and `OAI.InvariantIsing.cavityResolvent` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityRootedDepthTest`, `OAI.InvariantIsing.cavityRootedFullGibbs` and `OAI.InvariantIsing.cavityRootedFullGibbs_markov` (definitions bundle `OAIQ258003` of this split); `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.NoiseLeaf`, `OAI.IsingPerceptron.NoiseTree`, `OAI.IsingPerceptron.noiseCascadeLaw`, `OAI.IsingPerceptron.noiseLeafMeasurableSpace`, `OAI.IsingPerceptron.noiseTreeMeasurableSpace` and `OAI.IsingPerceptron.probabilityReplicaKernel` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_full_depth_test_evaluation` and `OAI.InvariantIsing.restricted_cavity_full_depth_test_evaluation` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityRootedDepthTransport.lean (declaration OAI.InvariantIsing.cavity_rooted_depth_test_transport)

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
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_rooted_depth_test_transport {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (hR : (H n).PosSemidef)
    (hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] (a : ℕ → ℝ) :
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    let J₀ := (1 - H 0 * K)⁻¹
    let P' := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (J₀ * S₀ * J₀.transpose)).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b
        (cavityGaussianMarks (fun i =>
          (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose)) : Measure _)
    (∫ σ, cavityRootedDepthTest a σ
      ∂((probabilityReplicaKernel (cavityRootedFullGibbs n K (H n) L C π)
        (cavityRootedFullGibbs n K (H n) L C π).measurable) ∘ₘ P)) =
    ∫ σ, cavityRootedDepthTest a σ
      ∂((probabilityReplicaKernel (cavityRootedFullGibbs n 0 (cavityResolvent K (H n)) L C π)
        (cavityRootedFullGibbs n 0 (cavityResolvent K (H n)) L C π).measurable) ∘ₘ P') := by
  sorry

end InvariantIsing

end

end OAI
end
