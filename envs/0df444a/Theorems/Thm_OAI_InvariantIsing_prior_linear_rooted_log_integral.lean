-- Prove2me | Theorems.Thm_OAI_InvariantIsing_prior_linear_rooted_log_integral
-- name    : OAI.InvariantIsing.prior_linear_rooted_log_integral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:30:20.053397+00:00
-- url     : https://prove2.me/theorems/bce14130-c968-4974-97db-066dd0954daa
-- title:
--   OAI.InvariantIsing.prior_linear_rooted_log_integral: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.prior_linear_rooted_log_integral` of [lean/OAI/Probability/InvariantIsing/Fields/PriorLinearLogEvaluation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/PriorLinearLogEvaluation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped Matrix NNReal`):
--
--   ```lean
--   theorem prior_linear_rooted_log_integral {d k : ℕ} (hk : 0 < k) (π : Measure (Spin k)) [IsProbabilityMeasure π] (h : FieldStep)
--       (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef)
--       (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
--       (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
--       (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
--       (hcov : ∀ i < h.depth, L.transpose * S i * L = (fieldStepVariance h i : ℝ) • 1)
--       (hres : L.transpose * R * L = (v : ℝ) • 1)
--       (hroot : L.transpose * S₀ * L = h.height 0 • 1)
--       (c : ℝ) :
--       let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
--         (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) h.depth (chainExponent h.cut)
--           (cavityGaussianMarks S) : Measure _)
--       Integrable (cavityRootedLogNormalizer h.depth 0 R L (c • 1) π) P ∧
--         (∫ p, cavityRootedLogNormalizer h.depth 0 R L (c • 1) π p ∂P) =
--         (k : ℝ) * (c + v) / 2 +
--           ∫ z, cascadeRecursion h.depth (chainExponent h.cut)
--             (fun i => vectorGaussianLaw k (fieldStepVariance h i))
--             (fun _ p => p.1 + p.2) (fun y => finiteLogIntegral π (fieldEnergy y)) z
--             ∂(vectorGaussianLaw k (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure _)
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.cavityGaussianMarks` and `OAI.InvariantIsing.vectorGaussianLaw` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityRootedLogNormalizer` and `OAI.InvariantIsing.fieldStepVariance` (definitions bundle `OAIQ258003` of this split); `OAI.IsingPerceptron.NoiseTree`, `OAI.IsingPerceptron.cascadeRecursion`, `OAI.IsingPerceptron.chainExponent`, `OAI.IsingPerceptron.finiteLogIntegral`, `OAI.IsingPerceptron.noiseCascadeLaw` and `OAI.IsingPerceptron.noiseTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.FieldStep`, `OAI.InvariantIsing.Spin` and `OAI.InvariantIsing.fieldEnergy` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.prior_cavity_full_log_evaluation` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/PriorLinearLogEvaluation.lean (declaration OAI.InvariantIsing.prior_linear_rooted_log_integral)

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
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003

section

attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix NNReal

namespace InvariantIsing

theorem prior_linear_rooted_log_integral {d k : ℕ} (hk : 0 < k) (π : Measure (Spin k)) [IsProbabilityMeasure π] (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef)
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : ∀ i < h.depth, L.transpose * S i * L = (fieldStepVariance h i : ℝ) • 1)
    (hres : L.transpose * R * L = (v : ℝ) • 1)
    (hroot : L.transpose * S₀ * L = h.height 0 • 1)
    (c : ℝ) :
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) h.depth (chainExponent h.cut)
        (cavityGaussianMarks S) : Measure _)
    Integrable (cavityRootedLogNormalizer h.depth 0 R L (c • 1) π) P ∧
      (∫ p, cavityRootedLogNormalizer h.depth 0 R L (c • 1) π p ∂P) =
      (k : ℝ) * (c + v) / 2 +
        ∫ z, cascadeRecursion h.depth (chainExponent h.cut)
          (fun i => vectorGaussianLaw k (fieldStepVariance h i))
          (fun _ p => p.1 + p.2) (fun y => finiteLogIntegral π (fieldEnergy y)) z
          ∂(vectorGaussianLaw k (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure _) := by
  sorry

end InvariantIsing

end

end OAI
end
