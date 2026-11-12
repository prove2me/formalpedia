-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_finite_labeled_moment
-- name    : OAI.InvariantIsing.cavity_finite_labeled_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:21:24.768196+00:00
-- url     : https://prove2.me/theorems/d473fdf8-68f8-46c6-aca9-abc06bd71178
-- title:
--   OAI.InvariantIsing.cavity_finite_labeled_moment: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_finite_labeled_moment` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityFiniteLabeledMoment.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityFiniteLabeledMoment.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Set`, `open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators`):
--
--   ```lean
--   theorem cavity_finite_labeled_moment {m d N n k : ℕ}
--       (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
--       (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
--       (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
--       (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
--       (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
--       (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
--       (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
--       (htop : q (Fin.last n) < 1)
--       (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
--       (π : Measure (Spin k)) [IsProbabilityMeasure π] (ℓ : ℕ) :
--       let K := B.transpose * cavityRepeatedSpectrum (n := N) eig * B -
--         Matrix.diagonal (fun i => eig (g i))
--       let R := cavityFiniteCovariancePath ρ eig hρ hsum g p q n
--       let S := cavityFiniteNoiseCovariance ρ eig hρ hsum g p cut q
--       let S₀ := cavityFiniteRootCovariance ρ eig hρ hsum g p q
--       let P := cavityLabeledDisorderLaw n (chainExponent cut) S₀ S
--       (∀ᵐ ω ∂P, Integrable (fun x => Real.exp (cavityLabeledPotential n K L C (ω,x)))
--           (cavityLabeledPriorKernel n R π ω) ∧
--         Integrable (fun x => ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ)
--           ((cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x)))) ∧
--       Integrable (fun ω => ∫ x, ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ
--         ∂(cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x))) P ∧
--       (∫ ω, ∫ x, ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ
--         ∂(cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x)) ∂P) ≤
--         cavityGaussianLinearMomentBound d ℓ (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.CavityLabeledDisorder` and `OAI.InvariantIsing.CavityLabeledState` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.cavityGaussianLinearMomentBound`, `OAI.InvariantIsing.cavityMatrixMass` and `OAI.InvariantIsing.cavityRepeatedSpectrum` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityFiniteCovariancePath`, `OAI.InvariantIsing.cavityFiniteNoiseCovariance`, `OAI.InvariantIsing.cavityFiniteRootCovariance`, `OAI.InvariantIsing.cavityLabeledDisorderLaw`, `OAI.InvariantIsing.cavityLabeledEndpoint`, `OAI.InvariantIsing.cavityLabeledPotential` and `OAI.InvariantIsing.cavityLabeledPriorKernel` (definitions bundle `OAIQ258003` of this split); `OAI.IsingPerceptron.ForestVertex`, `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.chainExponent`, `OAI.IsingPerceptron.labeledLeafMeasurableSpace` and `OAI.IsingPerceptron.labeledTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.OverlapPath` and `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_finite_trial_preliminary_lower`, `OAI.InvariantIsing.cavity_haar_finite_cutoff_comparison` and `OAI.InvariantIsing.restricted_cavity_finite_trial_preliminary_lower` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityFiniteLabeledMoment.lean (declaration OAI.InvariantIsing.cavity_finite_labeled_moment)

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

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace InvariantIsing

theorem cavity_finite_labeled_moment {m d N n k : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] (ℓ : ℕ) :
    let K := B.transpose * cavityRepeatedSpectrum (n := N) eig * B -
      Matrix.diagonal (fun i => eig (g i))
    let R := cavityFiniteCovariancePath ρ eig hρ hsum g p q n
    let S := cavityFiniteNoiseCovariance ρ eig hρ hsum g p cut q
    let S₀ := cavityFiniteRootCovariance ρ eig hρ hsum g p q
    let P := cavityLabeledDisorderLaw n (chainExponent cut) S₀ S
    (∀ᵐ ω ∂P, Integrable (fun x => Real.exp (cavityLabeledPotential n K L C (ω,x)))
        (cavityLabeledPriorKernel n R π ω) ∧
      Integrable (fun x => ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ)
        ((cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x)))) ∧
    Integrable (fun ω => ∫ x, ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ
      ∂(cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x))) P ∧
    (∫ ω, ∫ x, ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ
      ∂(cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x)) ∂P) ≤
      cavityGaussianLinearMomentBound d ℓ (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹ := by
  sorry

end InvariantIsing

end

end OAI
end
