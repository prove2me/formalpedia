-- Prove2me | Theorems.Thm_OAI_InvariantIsing_restricted_cavity_finite_log_evaluation
-- name    : OAI.InvariantIsing.restricted_cavity_finite_log_evaluation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:31:37.463859+00:00
-- url     : https://prove2.me/theorems/6adc4040-5dfd-4f85-b52c-220cddb156af
-- title:
--   OAI.InvariantIsing.restricted_cavity_finite_log_evaluation: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.restricted_cavity_finite_log_evaluation` of [lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedFiniteLogEvaluation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedFiniteLogEvaluation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory Set IsingPerceptron`, `open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal`):
--
--   ```lean
--   theorem restricted_cavity_finite_log_evaluation
--       {m d N n : ℕ} (hN : 0 < N) (T : Finset (Spin N)) (hT : T.Nonempty)
--       (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
--       (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
--       (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
--       (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
--         (cavityLimitingStack (n := N) rho).transpose = 1)
--       (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
--       (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a ≤ N)
--       (hcounts : ∀ a, (Finset.univ.filter (fun i => g i = a)).card = N - counts a)
--       (hcounts_rho : ∀ a, (counts a : ℝ) = (N : ℝ) * rho a)
--       (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
--       (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
--       (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
--       (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
--       (htop : q (Fin.last n) < 1) :
--       let hq0 := fun i => (finite_overlap_value_mem_unit p cut hcut q hp i).1
--       let h := cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0
--       let H := cavityFiniteCovariancePath rho lam hrho hsum g p q
--       let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q
--       let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p q
--       let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
--         Matrix.diagonal (fun i => lam (g i))
--       let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
--       let c := finiteR rho lam hrho hsum 0
--       let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
--         (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n (chainExponent cut)
--           (cavityGaussianMarks S) : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n))
--       Integrable (cavityRootedLogNormalizer n K (H n) L (c • 1) (restrictedSpinPrior T hT)) P ∧
--         (N : ℝ)⁻¹ * (∫ ω, cavityRootedLogNormalizer n K (H n) L (c • 1)
--           (restrictedSpinPrior T hT) ω ∂P) + (N : ℝ)⁻¹ *
--           (Real.log T.card - N * Real.log 2) =
--           constrainedBlockValue T h + fieldPairing p h / 2 + spectralFunctional (finiteR rho lam hrho hsum) p
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.cavityGaussianMarks`, `OAI.InvariantIsing.cavityLimitingStack`, `OAI.InvariantIsing.cavityRepeatedSpectrum` and `OAI.InvariantIsing.finiteR` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityFieldStep`, `OAI.InvariantIsing.cavityFiniteCovariancePath`, `OAI.InvariantIsing.cavityFiniteNoiseCovariance`, `OAI.InvariantIsing.cavityFiniteRootCovariance`, `OAI.InvariantIsing.cavityRootedLogNormalizer`, `OAI.InvariantIsing.constrainedBlockValue` and `OAI.InvariantIsing.restrictedSpinPrior` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.finite_overlap_value_mem_unit` (definitions bundle `OAIQ258004` of this split); `OAI.IsingPerceptron.NoiseTree`, `OAI.IsingPerceptron.chainExponent`, `OAI.IsingPerceptron.noiseCascadeLaw` and `OAI.IsingPerceptron.noiseTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.FieldStep`, `OAI.InvariantIsing.OverlapPath`, `OAI.InvariantIsing.Spin`, `OAI.InvariantIsing.fieldPairing` and `OAI.InvariantIsing.spectralFunctional` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.restricted_cavity_finite_trial_preliminary_lower` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/RestrictedFiniteLogEvaluation.lean (declaration OAI.InvariantIsing.restricted_cavity_finite_log_evaluation)

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
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.InformationTheory.KullbackLeibler.Basic
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
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Definitions.Def_OAIQ258004

section

attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal

namespace InvariantIsing

theorem restricted_cavity_finite_log_evaluation
    {m d N n : ℕ} (hN : 0 < N) (T : Finset (Spin N)) (hT : T.Nonempty)
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
      (cavityLimitingStack (n := N) rho).transpose = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a ≤ N)
    (hcounts : ∀ a, (Finset.univ.filter (fun i => g i = a)).card = N - counts a)
    (hcounts_rho : ∀ a, (counts a : ℝ) = (N : ℝ) * rho a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) :
    let hq0 := fun i => (finite_overlap_value_mem_unit p cut hcut q hp i).1
    let h := cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0
    let H := cavityFiniteCovariancePath rho lam hrho hsum g p q
    let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q
    let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p q
    let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
      Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
    let c := finiteR rho lam hrho hsum 0
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n (chainExponent cut)
        (cavityGaussianMarks S) : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n))
    Integrable (cavityRootedLogNormalizer n K (H n) L (c • 1) (restrictedSpinPrior T hT)) P ∧
      (N : ℝ)⁻¹ * (∫ ω, cavityRootedLogNormalizer n K (H n) L (c • 1)
        (restrictedSpinPrior T hT) ω ∂P) + (N : ℝ)⁻¹ *
        (Real.log T.card - N * Real.log 2) =
        constrainedBlockValue T h + fieldPairing p h / 2 + spectralFunctional (finiteR rho lam hrho hsum) p := by
  sorry

end InvariantIsing

end

end OAI
end
