-- Prove2me | Theorems.Thm_OAI_InvariantIsing_tensor_envelope_pressure_lower
-- name    : OAI.InvariantIsing.tensor_envelope_pressure_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:45:53.394034+00:00
-- url     : https://prove2.me/theorems/49964b99-daf5-4349-86a7-eeb47ba84641
-- title:
--   OAI.InvariantIsing.tensor_envelope_pressure_lower: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.tensor_envelope_pressure_lower` of [lean/OAI/Probability/InvariantIsing/Arrays/TensorEnvelopeLower.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorEnvelopeLower.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem tensor_envelope_pressure_lower
--       (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
--       (m depth N₀ n : ℕ) (hN₀ : 3≤N₀) (hn : 0<n)
--       (b : ℕ → ℝ) (hb : CascadeExponents depth b)
--       (μ : (N : ℕ) → Measure (SpecialOrthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
--       (hμ : ∀ N, (μ N).IsMulLeftInvariant)
--       (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
--       (u : (N : ℕ) → Fin N → ℝ) (v : ℕ → Fin m → ℝ)
--       (hu : ∀ N j, u N j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ N a, v N a ∈ Set.Icc (1 : ℝ) 2)
--       (hmin : ∀ N, 3≤N → ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
--         (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
--         tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b
--           (fun _ => 0) (u N) (v N) ≤
--         tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b (fun _ => 0) u' v')
--       (L : ℝ)
--       (hlower : ∀ ε>0, ∀ᶠ r in atTop,
--         let N := N₀+n*r
--         L-ε ≤ ((N+n : ℝ)*tensorPerturbationPressureMean (μ (N+n)) (eig (N+n)) (c (N+n))
--           (I (N+n)) (fun j => cavityBaseAmplitude (u N) j) (v N) 1 depth b (fun _ => 0) -
--           (N : ℝ)*tensorPerturbationPressureMean (μ N) (eig N) (c N) (I N)
--             (u N) (v N) 1 depth b (fun _ => 0))/(n : ℝ)) :
--       ∀ ε>0, ∀ᶠ r in atTop, L-ε ≤
--         ∫ U, rotatedPressure (eig (N₀+n*r)) (specialRotation U) (c (N₀+n*r)) ∂μ (N₀+n*r)
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.GaussianLipschitzVarianceInput`, `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.cavityBaseAmplitude` and `OAI.InvariantIsing.specialRotation` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.HaarConcentrationInput` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.tensorPerturbationObjective` and `OAI.InvariantIsing.tensorPerturbationPressureMean` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.CascadeExponents` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.rotatedPressure` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.CompactSpectralPartition.pressure_tendsto` and `OAI.InvariantIsing.CompactSpectralPartition.selected_pressure_tendsto` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorEnvelopeLower.lean (declaration OAI.InvariantIsing.tensor_envelope_pressure_lower)

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

attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem tensor_envelope_pressure_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (m depth N₀ n : ℕ) (hN₀ : 3≤N₀) (hn : 0<n)
    (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    (hμ : ∀ N, (μ N).IsMulLeftInvariant)
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (u : (N : ℕ) → Fin N → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ N j, u N j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ N a, v N a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ N, 3≤N → ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b
        (fun _ => 0) (u N) (v N) ≤
      tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b (fun _ => 0) u' v')
    (L : ℝ)
    (hlower : ∀ ε>0, ∀ᶠ r in atTop,
      let N := N₀+n*r
      L-ε ≤ ((N+n : ℝ)*tensorPerturbationPressureMean (μ (N+n)) (eig (N+n)) (c (N+n))
        (I (N+n)) (fun j => cavityBaseAmplitude (u N) j) (v N) 1 depth b (fun _ => 0) -
        (N : ℝ)*tensorPerturbationPressureMean (μ N) (eig N) (c N) (I N)
          (u N) (v N) 1 depth b (fun _ => 0))/(n : ℝ)) :
    ∀ ε>0, ∀ᶠ r in atTop, L-ε ≤
      ∫ U, rotatedPressure (eig (N₀+n*r)) (specialRotation U) (c (N₀+n*r)) ∂μ (N₀+n*r) := by
  sorry

end InvariantIsing

end

end OAI
end
