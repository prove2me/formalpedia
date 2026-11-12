-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_finite_trial_preliminary_lower
-- name    : OAI.InvariantIsing.cavity_finite_trial_preliminary_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:20:43.048645+00:00
-- url     : https://prove2.me/theorems/3aa01764-494a-424f-b7a2-9b052e75bb22
-- title:
--   OAI.InvariantIsing.cavity_finite_trial_preliminary_lower: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_finite_trial_preliminary_lower` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityFiniteTrialLower.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityFiniteTrialLower.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set`, `open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal`):
--
--   ```lean
--   theorem cavity_finite_trial_preliminary_lower
--       {m d N : ℕ} (hN : 0 < N)
--       (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
--       (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
--       (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
--       (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
--         (cavityLimitingStack (n := N) rho).transpose = 1)
--       (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
--       (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a ≤ N)
--       (hcounts : ∀ a, (Finset.univ.filter (fun i => g i = a)).card = N - counts a)
--       (hcounts_rho : ∀ a, (counts a : ℝ) = (N : ℝ) * rho a)
--       (p : OverlapPath) (U : Rotation N)
--       (A : ℕ → ℝ) (cap : ℝ → ℕ → ℝ) (hu : ∀ T > 0, ∀ n, cap T n ≤ A n) :
--       let p' := cavityStrictUniformPath p
--       let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
--         Matrix.diagonal (fun i => lam (g i))
--       let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
--       let c := finiteR rho lam hrho hsum 0
--       let Q := fun n => cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
--         (cavityFiniteRootCovariance rho lam hrho hsum g (p' n) (cavityStrictUniformLevels p n))
--         (cavityFiniteNoiseCovariance rho lam hrho hsum g (p' n) (uniformCut n)
--           (cavityStrictUniformLevels p n))
--       let η := fun n => cavityLabeledPriorKernel n
--         (cavityFiniteCovariancePath rho lam hrho hsum g (p' n) (cavityStrictUniformLevels p n) n)
--         (uniformSpinPrior N)
--       (∀ T > 0, Tendsto (fun n => cap T n -
--         ∫ ω, Real.log (∫ x, Real.exp (min (cavityLabeledPotential n K L (c • 1) (ω,x)) T)
--           ∂η n ω) ∂Q n) atTop (𝓝 0)) →
--       ∀ ε > 0, ∀ᶠ n in atTop,
--         fieldValue (cavityStrictUniformField rho lam hrho hsum p n) 0 +
--           fieldPairing (p' n) (cavityStrictUniformField rho lam hrho hsum p n) / 2 +
--           spectralFunctional (finiteR rho lam hrho hsum) (p' n) - (N : ℝ)⁻¹ * A n < ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.CavityLabeledDisorder` and `OAI.InvariantIsing.CavityLabeledState` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.cavityLimitingStack`, `OAI.InvariantIsing.cavityRepeatedSpectrum` and `OAI.InvariantIsing.finiteR` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityFiniteCovariancePath`, `OAI.InvariantIsing.cavityFiniteNoiseCovariance`, `OAI.InvariantIsing.cavityFiniteRootCovariance`, `OAI.InvariantIsing.cavityLabeledDisorderLaw`, `OAI.InvariantIsing.cavityLabeledPotential`, `OAI.InvariantIsing.cavityLabeledPriorKernel`, `OAI.InvariantIsing.cavityStrictUniformField`, `OAI.InvariantIsing.cavityStrictUniformLevels`, `OAI.InvariantIsing.cavityStrictUniformPath` and `OAI.InvariantIsing.uniformSpinPrior` (definitions bundle `OAIQ258003` of this split); `OAI.IsingPerceptron.ForestVertex`, `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.chainExponent`, `OAI.IsingPerceptron.labeledLeafMeasurableSpace`, `OAI.IsingPerceptron.labeledTreeMeasurableSpace` and `OAI.IsingPerceptron.uniformCut` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.OverlapPath`, `OAI.InvariantIsing.Rotation`, `OAI.InvariantIsing.Spin`, `OAI.InvariantIsing.fieldPairing`, `OAI.InvariantIsing.fieldValue` and `OAI.InvariantIsing.spectralFunctional` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.cavity_physical_trial_lower` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityFiniteTrialLower.lean (declaration OAI.InvariantIsing.cavity_finite_trial_preliminary_lower)

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

attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal

namespace InvariantIsing

theorem cavity_finite_trial_preliminary_lower
    {m d N : ℕ} (hN : 0 < N)
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
      (cavityLimitingStack (n := N) rho).transpose = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a ≤ N)
    (hcounts : ∀ a, (Finset.univ.filter (fun i => g i = a)).card = N - counts a)
    (hcounts_rho : ∀ a, (counts a : ℝ) = (N : ℝ) * rho a)
    (p : OverlapPath) (U : Rotation N)
    (A : ℕ → ℝ) (cap : ℝ → ℕ → ℝ) (hu : ∀ T > 0, ∀ n, cap T n ≤ A n) :
    let p' := cavityStrictUniformPath p
    let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
      Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
    let c := finiteR rho lam hrho hsum 0
    let Q := fun n => cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
      (cavityFiniteRootCovariance rho lam hrho hsum g (p' n) (cavityStrictUniformLevels p n))
      (cavityFiniteNoiseCovariance rho lam hrho hsum g (p' n) (uniformCut n)
        (cavityStrictUniformLevels p n))
    let η := fun n => cavityLabeledPriorKernel n
      (cavityFiniteCovariancePath rho lam hrho hsum g (p' n) (cavityStrictUniformLevels p n) n)
      (uniformSpinPrior N)
    (∀ T > 0, Tendsto (fun n => cap T n -
      ∫ ω, Real.log (∫ x, Real.exp (min (cavityLabeledPotential n K L (c • 1) (ω,x)) T)
        ∂η n ω) ∂Q n) atTop (𝓝 0)) →
    ∀ ε > 0, ∀ᶠ n in atTop,
      fieldValue (cavityStrictUniformField rho lam hrho hsum p n) 0 +
        fieldPairing (p' n) (cavityStrictUniformField rho lam hrho hsum p n) / 2 +
        spectralFunctional (finiteR rho lam hrho hsum) (p' n) - (N : ℝ)⁻¹ * A n < ε := by
  sorry

end InvariantIsing

end

end OAI
end
