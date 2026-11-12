-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_finite_spin_test
-- name    : OAI.InvariantIsing.cavity_finite_spin_test
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:34:04.351286+00:00
-- url     : https://prove2.me/theorems/d907a40e-8585-4aac-96f3-71163afa6eec
-- title:
--   OAI.InvariantIsing.cavity_finite_spin_test: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_finite_spin_test` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityFiniteSpinTest.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityFiniteSpinTest.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory Set IsingPerceptron`, `open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal`):
--
--   ```lean
--   theorem cavity_finite_spin_test (hpub : PanchenkoTalagrandFieldPairInput)
--       {m d N n : ℕ} (hd : 0 < d) (hN : 0 < N)
--       (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
--       (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
--       (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
--       (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
--         (cavityLimitingStack (n := N) rho).transpose = 1)
--       (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
--       (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
--       (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
--       (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
--       (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
--       (htop : q (Fin.last n) < 1) (Φ : ℝ → ℝ) (j : Fin N)
--       {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
--       let hq0 := fun i => (finite_overlap_value_mem_unit p cut hcut q hp i).1
--       let h := cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0
--       let H := cavityFiniteCovariancePath rho lam hrho hsum g p q
--       let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q
--       let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p q
--       let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
--         Matrix.diagonal (fun i => lam (g i))
--       let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
--       let c := finiteR rho lam hrho hsum 0
--       (∫ σ, cavityRootedSpinDepthTest (fun i => Φ (q (fieldDepthLevel h i))) j σ
--         ∂((probabilityReplicaKernel
--           (cavityRootedFullGibbs n K (H n) L (c • 1) (uniformSpinPrior N))
--           (cavityRootedFullGibbs n K (H n) L (c • 1) (uniformSpinPrior N)).measurable)
--             ∘ₘ (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
--               (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n (chainExponent cut)
--                 (cavityGaussianMarks S) : Measure _))) =
--         ∫ t, Φ (p t) * fieldMagnetizationPath h t ∂pathMeasure
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.cavityGaussianMarks`, `OAI.InvariantIsing.cavityLimitingStack`, `OAI.InvariantIsing.cavityRepeatedSpectrum`, `OAI.InvariantIsing.fieldDepthLevel` and `OAI.InvariantIsing.finiteR` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.PanchenkoTalagrandFieldPairInput`, `OAI.InvariantIsing.cavityFieldStep`, `OAI.InvariantIsing.cavityFiniteCovariancePath`, `OAI.InvariantIsing.cavityFiniteNoiseCovariance`, `OAI.InvariantIsing.cavityFiniteRootCovariance`, `OAI.InvariantIsing.cavityRootedFullGibbs`, `OAI.InvariantIsing.cavityRootedFullGibbs_markov`, `OAI.InvariantIsing.cavityRootedSpinDepthTest` and `OAI.InvariantIsing.uniformSpinPrior` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.finite_overlap_value_mem_unit` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.fieldMagnetizationPath` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.NoiseLeaf`, `OAI.IsingPerceptron.NoiseTree`, `OAI.IsingPerceptron.chainExponent`, `OAI.IsingPerceptron.noiseCascadeLaw`, `OAI.IsingPerceptron.noiseLeafMeasurableSpace`, `OAI.IsingPerceptron.noiseTreeMeasurableSpace` and `OAI.IsingPerceptron.probabilityReplicaKernel` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.FieldStep`, `OAI.InvariantIsing.OverlapPath`, `OAI.InvariantIsing.Spin` and `OAI.InvariantIsing.pathMeasure` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.cavity_physical_spin_cutoff` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityFiniteSpinTest.lean (declaration OAI.InvariantIsing.cavity_finite_spin_test)

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
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal

namespace InvariantIsing

theorem cavity_finite_spin_test (hpub : PanchenkoTalagrandFieldPairInput)
    {m d N n : ℕ} (hd : 0 < d) (hN : 0 < N)
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
      (cavityLimitingStack (n := N) rho).transpose = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (Φ : ℝ → ℝ) (j : Fin N)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    let hq0 := fun i => (finite_overlap_value_mem_unit p cut hcut q hp i).1
    let h := cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0
    let H := cavityFiniteCovariancePath rho lam hrho hsum g p q
    let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q
    let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p q
    let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
      Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
    let c := finiteR rho lam hrho hsum 0
    (∫ σ, cavityRootedSpinDepthTest (fun i => Φ (q (fieldDepthLevel h i))) j σ
      ∂((probabilityReplicaKernel
        (cavityRootedFullGibbs n K (H n) L (c • 1) (uniformSpinPrior N))
        (cavityRootedFullGibbs n K (H n) L (c • 1) (uniformSpinPrior N)).measurable)
          ∘ₘ (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
            (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n (chainExponent cut)
              (cavityGaussianMarks S) : Measure _))) =
      ∫ t, Φ (p t) * fieldMagnetizationPath h t ∂pathMeasure := by
  sorry

end InvariantIsing

end

end OAI
end
