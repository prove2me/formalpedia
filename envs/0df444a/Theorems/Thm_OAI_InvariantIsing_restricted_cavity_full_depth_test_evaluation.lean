-- Prove2me | Theorems.Thm_OAI_InvariantIsing_restricted_cavity_full_depth_test_evaluation
-- name    : OAI.InvariantIsing.restricted_cavity_full_depth_test_evaluation
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:31:46.637198+00:00
-- url     : https://prove2.me/theorems/5f821ad0-3fdc-4cba-8178-cc1b3b6e57e5
-- title:
--   OAI.InvariantIsing.restricted_cavity_full_depth_test_evaluation: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.restricted_cavity_full_depth_test_evaluation` of [lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedDepthTestEvaluation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedDepthTestEvaluation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped Matrix MatrixOrder Matrix.Norms.L2Operator NNReal`):
--
--   ```lean
--   theorem restricted_cavity_full_depth_test_evaluation (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
--       {d k : ℕ} (hk : 0 < k) (T : Finset (Spin k)) (hT : T.Nonempty) (h : FieldStep)
--       (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ)
--       (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
--       (L : Matrix (Fin d) (Fin k) ℝ) (c : ℝ)
--       (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
--       (hS : ∀ i, (S i).PosSemidef)
--       (hb : ∀ i, 0 < chainExponent h.cut i)
--       (hdet : ∀ i, IsUnit (1 - H i * K).det)
--       (hΔ : ∀ i, H i - H (i + 1) = chainExponent h.cut i • S i)
--       (hQ : ∀ i, (cavityFactorPrecision
--         (chainExponent h.cut i • cavityBackwardQuadratic K (H (i + 1)))
--           (CFC.sqrt (S i))).PosDef)
--       (hR : (H h.depth).PosSemidef)
--       (hQR : (cavityFactorPrecision K (CFC.sqrt (H h.depth))).PosDef)
--       (hAtom : ∀ i < h.depth,
--         NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S i)))
--       (v : ℝ≥0)
--       (hcov : ∀ i < h.depth,
--         L.transpose * ((1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose) * L =
--           (fieldStepVariance h i : ℝ) • 1)
--       (hres : L.transpose * cavityResolvent K (H h.depth) * L = (v : ℝ) • 1)
--       (ψ : ℕ → ℝ)
--       {B : ℝ} (hψ : ∀ i, |ψ i| ≤ B) :
--       (∫ σ, cavityRootedDepthTest ψ σ
--         ∂((probabilityReplicaKernel
--           (cavityRootedFullGibbs h.depth K (H h.depth) L (c • 1) (restrictedSpinPrior T hT))
--           (cavityRootedFullGibbs h.depth K (H h.depth) L (c • 1) (restrictedSpinPrior T hT)).measurable)
--             ∘ₘ (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
--               (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) h.depth (chainExponent h.cut)
--                 (cavityGaussianMarks S) : Measure _))) =
--         ∫ t, ψ (fieldLevelIndex h t).val ∂pathMeasure
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.cavityBackwardQuadratic`, `OAI.InvariantIsing.cavityFactorPrecision`, `OAI.InvariantIsing.cavityGaussianMarks` and `OAI.InvariantIsing.cavityResolvent` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.fieldLevelIndex` (definitions bundle `OAIQ258002` of this split); `OAI.InvariantIsing.PanchenkoTalagrandRestrictedFieldPairInput`, `OAI.InvariantIsing.cavityRootedDepthTest`, `OAI.InvariantIsing.cavityRootedFullGibbs`, `OAI.InvariantIsing.cavityRootedFullGibbs_markov`, `OAI.InvariantIsing.fieldStepVariance` and `OAI.InvariantIsing.restrictedSpinPrior` (definitions bundle `OAIQ258003` of this split); `OAI.IsingPerceptron.NoiseLeaf`, `OAI.IsingPerceptron.NoiseTree`, `OAI.IsingPerceptron.chainExponent`, `OAI.IsingPerceptron.noiseCascadeLaw`, `OAI.IsingPerceptron.noiseLeafMeasurableSpace`, `OAI.IsingPerceptron.noiseTreeMeasurableSpace` and `OAI.IsingPerceptron.probabilityReplicaKernel` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.FieldStep`, `OAI.InvariantIsing.Spin` and `OAI.InvariantIsing.pathMeasure` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.restricted_original_split_overlap_limit` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedDepthTestEvaluation.lean (declaration OAI.InvariantIsing.restricted_cavity_full_depth_test_evaluation)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
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
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator NNReal

namespace InvariantIsing

theorem restricted_cavity_full_depth_test_evaluation (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {d k : ℕ} (hk : 0 < k) (T : Finset (Spin k)) (hT : T.Nonempty) (h : FieldStep)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (c : ℝ)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef)
    (hb : ∀ i, 0 < chainExponent h.cut i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = chainExponent h.cut i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (chainExponent h.cut i • cavityBackwardQuadratic K (H (i + 1)))
        (CFC.sqrt (S i))).PosDef)
    (hR : (H h.depth).PosSemidef)
    (hQR : (cavityFactorPrecision K (CFC.sqrt (H h.depth))).PosDef)
    (hAtom : ∀ i < h.depth,
      NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S i)))
    (v : ℝ≥0)
    (hcov : ∀ i < h.depth,
      L.transpose * ((1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose) * L =
        (fieldStepVariance h i : ℝ) • 1)
    (hres : L.transpose * cavityResolvent K (H h.depth) * L = (v : ℝ) • 1)
    (ψ : ℕ → ℝ)
    {B : ℝ} (hψ : ∀ i, |ψ i| ≤ B) :
    (∫ σ, cavityRootedDepthTest ψ σ
      ∂((probabilityReplicaKernel
        (cavityRootedFullGibbs h.depth K (H h.depth) L (c • 1) (restrictedSpinPrior T hT))
        (cavityRootedFullGibbs h.depth K (H h.depth) L (c • 1) (restrictedSpinPrior T hT)).measurable)
          ∘ₘ (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
            (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) h.depth (chainExponent h.cut)
              (cavityGaussianMarks S) : Measure _))) =
      ∫ t, ψ (fieldLevelIndex h t).val ∂pathMeasure := by
  sorry

end InvariantIsing

end

end OAI
end
