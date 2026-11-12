-- Prove2me | Theorems.Thm_OAI_InvariantIsing_offset_envelope_pressure_lower
-- name    : OAI.InvariantIsing.offset_envelope_pressure_lower
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:39:56.6462+00:00
-- url     : https://prove2.me/theorems/63bf02dd-fd3d-418c-867f-1802f65e4c7e
-- title:
--   OAI.InvariantIsing.offset_envelope_pressure_lower: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.offset_envelope_pressure_lower` of [lean/OAI/Probability/InvariantIsing/Cavity/OffsetEnvelopeLower.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/OffsetEnvelopeLower.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem offset_envelope_pressure_lower
--       (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
--       {m n q r₀ : ℕ} (hn : 0 < n) (hq : 3 ≤ r₀+q*n)
--       (μ : (N : ℕ) → Measure (SpecialOrthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
--       (hμ : ∀ N, 3 ≤ N → (μ N).IsMulLeftInvariant)
--       (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
--       (R : Finset (Spin r₀)) (hR : R.Nonempty)
--       (C : Finset (Spin n)) (hC : C.Nonempty)
--       (u : (r : ℕ) → Fin (r₀+(q+r)*n) → ℝ) (v : ℕ → Fin m → ℝ)
--       (hu : ∀ r i, u r i ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ r a, v r a ∈ Set.Icc (1 : ℝ) 2)
--       (hmin : ∀ r u' v', (∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) →
--         (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
--         offsetPriorObjective μ eig c I q R hR C hC r (u r) (v r) ≤
--           offsetPriorObjective μ eig c I q R hR C hC r u' v')
--       (L : ℝ)
--       (hlower : ∀ ε > 0, ∀ᶠ r in atTop, L-ε ≤
--         (offsetPriorIncrement μ eig c I q R hR C hC u v r +
--           (Real.log C.card-n*Real.log 2))/(n : ℝ)) :
--       ∀ ε > 0, ∀ᶠ r in atTop, L-ε ≤
--         ∫ U, restrictedRotatedPressure (offsetBlockConstraint (q+r) R C)
--           (eig (r₀+(q+r)*n)) (specialRotation U) (c (r₀+(q+r)*n)) ∂μ (r₀+(q+r)*n)
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.GaussianLipschitzVarianceInput`, `OAI.InvariantIsing.SpecialOrthogonal` and `OAI.InvariantIsing.specialRotation` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.HaarConcentrationInput` and `OAI.InvariantIsing.offsetBlockConstraint` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.restrictedRotatedPressure` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.offsetPriorIncrement` and `OAI.InvariantIsing.offsetPriorObjective` (definitions bundle `OAIQ258005` of this split); `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.magnetic_affine_field_subsequence_lower` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/OffsetEnvelopeLower.lean (declaration OAI.InvariantIsing.offset_envelope_pressure_lower)

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
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Pi
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
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology
namespace InvariantIsing

theorem offset_envelope_pressure_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {m n q r₀ : ℕ} (hn : 0 < n) (hq : 3 ≤ r₀+q*n)
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    (hμ : ∀ N, 3 ≤ N → (μ N).IsMulLeftInvariant)
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (R : Finset (Spin r₀)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (u : (r : ℕ) → Fin (r₀+(q+r)*n) → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ r i, u r i ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ r a, v r a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ r u' v', (∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      offsetPriorObjective μ eig c I q R hR C hC r (u r) (v r) ≤
        offsetPriorObjective μ eig c I q R hR C hC r u' v')
    (L : ℝ)
    (hlower : ∀ ε > 0, ∀ᶠ r in atTop, L-ε ≤
      (offsetPriorIncrement μ eig c I q R hR C hC u v r +
        (Real.log C.card-n*Real.log 2))/(n : ℝ)) :
    ∀ ε > 0, ∀ᶠ r in atTop, L-ε ≤
      ∫ U, restrictedRotatedPressure (offsetBlockConstraint (q+r) R C)
        (eig (r₀+(q+r)*n)) (specialRotation U) (c (r₀+(q+r)*n)) ∂μ (r₀+(q+r)*n) := by
  sorry

end InvariantIsing

end

end OAI
end
