-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_strict_recalculated_gaussian_error
-- name    : OAI.InvariantIsing.cavity_strict_recalculated_gaussian_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:24:19.714243+00:00
-- url     : https://prove2.me/theorems/988c2bcd-2740-4495-85b2-b06cab3f94a6
-- title:
--   OAI.InvariantIsing.cavity_strict_recalculated_gaussian_error: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_strict_recalculated_gaussian_error` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityStrictGaussianLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityStrictGaussianLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter`, `open scoped BigOperators Topology BoundedContinuousFunction`):
--
--   ```lean
--   theorem cavity_strict_recalculated_gaussian_error {m r k : ℕ}
--       (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
--       (p : OverlapPath)
--       (F : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin k)) →ᵇ ℝ) :
--       let B := fun p' : OverlapPath => fun x : JointArray =>
--         cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p')
--           (cavityCanonicalLabel rho lam hrho hsum p') (arrayBlock spinArray r x)
--       Tendsto (fun n =>
--         (∫ x, ∫ z, F (B (cavityStrictUniformPath p n) x, z)
--           ∂multivariateGaussian 0 (cavityGroupBlockCovariance k rho (B (cavityStrictUniformPath p n) x))
--           ∂(cascadeCompactLaw n (uniformExponent n)
--             (fun i => cavityStrictUniformLevels p n (cavityFiniteLevel n i)) : Measure JointArray)) -
--         ∫ x, ∫ z, F (B p x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k rho (B p x))
--           ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray))
--         atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.SpectralBlock`, `OAI.InvariantIsing.SpectralEntry`, `OAI.InvariantIsing.cavityCanonicalLabel`, `OAI.InvariantIsing.cavityFiniteLevel`, `OAI.InvariantIsing.cavityGroupBlockCovariance` and `OAI.InvariantIsing.cavitySynchronizedBlock` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityCanonicalDiagonal`, `OAI.InvariantIsing.cavityStrictUniformLevels` and `OAI.InvariantIsing.cavityStrictUniformPath` (definitions bundle `OAIQ258003` of this split); `OAI.IsingPerceptron.JointArray`, `OAI.IsingPerceptron.JointEntry`, `OAI.IsingPerceptron.arrayBlock`, `OAI.IsingPerceptron.cascadeCompactLaw`, `OAI.IsingPerceptron.spinArray`, `OAI.IsingPerceptron.uniformCellAverage` and `OAI.IsingPerceptron.uniformExponent` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.OverlapPath` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_haar_gibbs_numerator_match` and `OAI.InvariantIsing.cavity_haar_strict_restricted_spin_match` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityStrictGaussianLimit.lean (declaration OAI.InvariantIsing.cavity_strict_recalculated_gaussian_error)

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
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
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

attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_strict_recalculated_gaussian_error {m r k : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath)
    (F : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin k)) →ᵇ ℝ) :
    let B := fun p' : OverlapPath => fun x : JointArray =>
      cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p')
        (cavityCanonicalLabel rho lam hrho hsum p') (arrayBlock spinArray r x)
    Tendsto (fun n =>
      (∫ x, ∫ z, F (B (cavityStrictUniformPath p n) x, z)
        ∂multivariateGaussian 0 (cavityGroupBlockCovariance k rho (B (cavityStrictUniformPath p n) x))
        ∂(cascadeCompactLaw n (uniformExponent n)
          (fun i => cavityStrictUniformLevels p n (cavityFiniteLevel n i)) : Measure JointArray)) -
      ∫ x, ∫ z, F (B p x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k rho (B p x))
        ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray))
      atTop (𝓝 0) := by
  sorry

end InvariantIsing

end

end OAI
end
