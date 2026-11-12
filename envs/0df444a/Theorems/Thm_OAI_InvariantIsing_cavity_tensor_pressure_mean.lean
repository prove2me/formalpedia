-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_tensor_pressure_mean
-- name    : OAI.InvariantIsing.cavity_tensor_pressure_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:36:28.891241+00:00
-- url     : https://prove2.me/theorems/bbaef4a4-6429-4599-a1b9-aaca595c3aa4
-- title:
--   OAI.InvariantIsing.cavity_tensor_pressure_mean: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_tensor_pressure_mean` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityTensorPressureMean.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityTensorPressureMean.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`):
--
--   ```lean
--   theorem cavity_tensor_pressure_mean {N m depth : ℕ} (hN : 0<N)
--       (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
--       (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
--       (u : ℕ → ℝ) (v : Fin m → ℝ) (t : ℝ)
--       (b : ℕ → ℝ) (hb : CascadeExponents depth b) :
--       (∫ p, cavityRotationLogMean p.2 (diagonalPerturbedEigenvalues eig I v t) I u p.1
--         ∂μ.prod (labeledCascadeLaw depth b : Measure (LabeledTree depth))) =
--         (N : ℝ)*tensorPerturbationPressureMean (cavityOrientedBaseLaw hN μ) eig (fun _ => 0) I
--           (fun j => u j) v t depth b (fun _ => 0)
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.diagonalPerturbedEigenvalues` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityOrientedBaseLaw` and `OAI.InvariantIsing.cavityRotationLogMean` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.tensorPerturbationPressureMean` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.labeledCascadeLaw` and `OAI.IsingPerceptron.labeledTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Orthogonal` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.CompactSpectralPartition.pressure_tendsto` and `OAI.InvariantIsing.CompactSpectralPartition.selected_pressure_tendsto` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityTensorPressureMean.lean (declaration OAI.InvariantIsing.cavity_tensor_pressure_mean)

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
import Mathlib.MeasureTheory.Group.LIntegral
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
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_tensor_pressure_mean {N m depth : ℕ} (hN : 0<N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : ℕ → ℝ) (v : Fin m → ℝ) (t : ℝ)
    (b : ℕ → ℝ) (hb : CascadeExponents depth b) :
    (∫ p, cavityRotationLogMean p.2 (diagonalPerturbedEigenvalues eig I v t) I u p.1
      ∂μ.prod (labeledCascadeLaw depth b : Measure (LabeledTree depth))) =
      (N : ℝ)*tensorPerturbationPressureMean (cavityOrientedBaseLaw hN μ) eig (fun _ => 0) I
        (fun j => u j) v t depth b (fun _ => 0) := by
  sorry

end InvariantIsing

end

end OAI
end
