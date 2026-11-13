-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_strict_finite_overlap_test
-- name    : OAI.InvariantIsing.cavity_strict_finite_overlap_test
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:24:42.109286+00:00
-- url     : https://prove2.me/theorems/4570c501-7f3f-436b-89ae-7e91d0038490
-- title:
--   OAI.InvariantIsing.cavity_strict_finite_overlap_test: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_strict_finite_overlap_test` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityStrictFiniteOverlap.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityStrictFiniteOverlap.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory Set IsingPerceptron`, `open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal`):
--
--   ```lean
--   theorem cavity_strict_finite_overlap_test (hpub : PanchenkoTalagrandFieldPairInput)
--       {m d N n : ℕ} (hd : 0 < d) (hN : 0 < N)
--       (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
--       (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
--       (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
--       (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
--         (cavityLimitingStack (n := N) rho).transpose = 1)
--       (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
--       (p : OverlapPath) (Φ : ℝ → ℝ) (hΦc : Continuous Φ)
--       {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
--       let q := cavityStrictUniformLevels p n
--       let p' := cavityStrictUniformPath p n
--       let H := cavityFiniteCovariancePath rho lam hrho hsum g p' q
--       let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p' (uniformCut n) q
--       let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p' q
--       let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
--         Matrix.diagonal (fun i => lam (g i))
--       let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
--       let c := finiteR rho lam hrho hsum 0
--       (∫ ω, cavityWeightedReplicaMean
--         (cavityLabeledPriorKernel n (H n) (uniformSpinPrior N) ω)
--         (fun x => Real.exp (cavityLabeledPotential n K L (c • 1) (ω,x)))
--         (fun ξ => cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p' q)
--           (cavityOverlapObservable Φ hΦc) (ω,ξ))
--         ∂cavityLabeledDisorderLaw n (chainExponent (uniformCut n)) S₀ S) =
--         ∫ t, Φ (p' t)
--           ∂pathMeasure
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.CavityLabeledDisorder` and `OAI.InvariantIsing.CavityLabeledState` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.cavityLimitingStack`, `OAI.InvariantIsing.cavityRepeatedSpectrum`, `OAI.InvariantIsing.cavityWeightedReplicaMean` and `OAI.InvariantIsing.finiteR` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.PanchenkoTalagrandFieldPairInput`, `OAI.InvariantIsing.cavityFiniteCovariancePath`, `OAI.InvariantIsing.cavityFiniteNoiseCovariance`, `OAI.InvariantIsing.cavityFiniteReplicaSpectralBlock`, `OAI.InvariantIsing.cavityFiniteRootCovariance`, `OAI.InvariantIsing.cavityLabeledDisorderLaw`, `OAI.InvariantIsing.cavityLabeledPotential`, `OAI.InvariantIsing.cavityLabeledPriorKernel`, `OAI.InvariantIsing.cavityLabeledReplicaTest`, `OAI.InvariantIsing.cavityOverlapObservable`, `OAI.InvariantIsing.cavityStrictUniformLevels`, `OAI.InvariantIsing.cavityStrictUniformPath` and `OAI.InvariantIsing.uniformSpinPrior` (definitions bundle `OAIQ258003` of this split); `OAI.IsingPerceptron.ForestVertex`, `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.chainExponent`, `OAI.IsingPerceptron.labeledLeafMeasurableSpace`, `OAI.IsingPerceptron.labeledTreeMeasurableSpace` and `OAI.IsingPerceptron.uniformCut` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.OverlapPath`, `OAI.InvariantIsing.Spin` and `OAI.InvariantIsing.pathMeasure` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.cavity_original_overlap_limit` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityStrictFiniteOverlap.lean (declaration OAI.InvariantIsing.cavity_strict_finite_overlap_test)

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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
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
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal

namespace InvariantIsing

theorem cavity_strict_finite_overlap_test (hpub : PanchenkoTalagrandFieldPairInput)
    {m d N n : ℕ} (hd : 0 < d) (hN : 0 < N)
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
      (cavityLimitingStack (n := N) rho).transpose = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (p : OverlapPath) (Φ : ℝ → ℝ) (hΦc : Continuous Φ)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    let q := cavityStrictUniformLevels p n
    let p' := cavityStrictUniformPath p n
    let H := cavityFiniteCovariancePath rho lam hrho hsum g p' q
    let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p' (uniformCut n) q
    let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p' q
    let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
      Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
    let c := finiteR rho lam hrho hsum 0
    (∫ ω, cavityWeightedReplicaMean
      (cavityLabeledPriorKernel n (H n) (uniformSpinPrior N) ω)
      (fun x => Real.exp (cavityLabeledPotential n K L (c • 1) (ω,x)))
      (fun ξ => cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p' q)
        (cavityOverlapObservable Φ hΦc) (ω,ξ))
      ∂cavityLabeledDisorderLaw n (chainExponent (uniformCut n)) S₀ S) =
      ∫ t, Φ (p' t)
        ∂pathMeasure := by
  sorry

end InvariantIsing

end

end OAI
end
