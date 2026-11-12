-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_spectral_haar_test_tendsto
-- name    : OAI.InvariantIsing.cavity_spectral_haar_test_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:15:52.845142+00:00
-- url     : https://prove2.me/theorems/672cb511-dd9e-4453-93c3-b5fb7630ccad
-- title:
--   OAI.InvariantIsing.cavity_spectral_haar_test_tendsto: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_spectral_haar_test_tendsto` of [lean/OAI/Probability/InvariantIsing/Cavity/CavitySpectralHaarLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavitySpectralHaarLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set`, `open scoped Topology BoundedContinuousFunction`):
--
--   ```lean
--   theorem cavity_spectral_haar_test_tendsto {m r q : ℕ}
--       (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
--       (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
--       [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
--       (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
--       (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
--       (X : ℕ → Type*) [∀ k, MeasurableSpace (X k)]
--       (P : (k : ℕ) → Measure (X k)) [∀ k, IsProbabilityMeasure (P k)]
--       (a : (k : ℕ) → X k → SpectralArray (m + 1)) (ha : ∀ k, Measurable (a k))
--       (hGram : ∀ k x, SpectralGram (a k x))
--       (v : (k : ℕ) → X k → (j : Fin m) → Fin r → Fin (N k j) → ℝ)
--       (hvM : ∀ k, Measurable (v k)) (C : ℝ)
--       (hv : ∀ k x j i l, |cavityGroupReplicaGram (v k x) j i l| ≤ C)
--       (ρs : ℕ → Fin m → ℝ) (ρ : Fin m → ℝ)
--       (hρ : Tendsto ρs atTop (𝓝 ρ)) (hρs : ∀ k j, 0 < ρs k j) (hρ0 : ∀ j, 0 < ρ j)
--       (hcov : ∀ k x, cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x)) =
--         cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r (a k x)))
--       (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
--       (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
--       (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (P k).map (a k))
--       (hlim : Tendsto Q atTop (𝓝 Q₀))
--       (F : SpectralBlock (m + 1) r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
--       Tendsto (fun k => ∫ x, ∫ U,
--         F (spectralBlockView (m + 1) r (a k x),
--           cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U))
--         ∂Measure.pi (μ k) ∂P k) atTop
--         (𝓝 (∫ x, ∫ y, F (spectralBlockView (m + 1) r x, y)
--           ∂multivariateGaussian 0
--             (cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x))
--           ∂(Q₀ : Measure (SpectralArray (m + 1)))))
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpectralArray`, `OAI.InvariantIsing.SpectralBlock`, `OAI.InvariantIsing.SpectralEntry`, `OAI.InvariantIsing.SpectralGram`, `OAI.InvariantIsing.cavityGroupHaarFrames`, `OAI.InvariantIsing.cavityGroupMatrixProjection`, `OAI.InvariantIsing.cavityGroupReplicaCovariance`, `OAI.InvariantIsing.cavityGroupReplicaGram`, `OAI.InvariantIsing.cavitySpectralBlockCovariance` and `OAI.InvariantIsing.spectralBlockView` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.Orthogonal` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_haar_gibbs_numerator_match` and `OAI.InvariantIsing.cavity_haar_strict_restricted_spin_match` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavitySpectralHaarLimit.lean (declaration OAI.InvariantIsing.cavity_spectral_haar_test_tendsto)

import Mathlib
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258000
import Definitions.Def_OAIQ258001

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_spectral_haar_test_tendsto {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (X : ℕ → Type*) [∀ k, MeasurableSpace (X k)]
    (P : (k : ℕ) → Measure (X k)) [∀ k, IsProbabilityMeasure (P k)]
    (a : (k : ℕ) → X k → SpectralArray (m + 1)) (ha : ∀ k, Measurable (a k))
    (hGram : ∀ k x, SpectralGram (a k x))
    (v : (k : ℕ) → X k → (j : Fin m) → Fin r → Fin (N k j) → ℝ)
    (hvM : ∀ k, Measurable (v k)) (C : ℝ)
    (hv : ∀ k x j i l, |cavityGroupReplicaGram (v k x) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ : Fin m → ℝ)
    (hρ : Tendsto ρs atTop (𝓝 ρ)) (hρs : ∀ k j, 0 < ρs k j) (hρ0 : ∀ j, 0 < ρ j)
    (hcov : ∀ k x, cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x)) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r (a k x)))
    (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
    (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (P k).map (a k))
    (hlim : Tendsto Q atTop (𝓝 Q₀))
    (F : SpectralBlock (m + 1) r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    Tendsto (fun k => ∫ x, ∫ U,
      F (spectralBlockView (m + 1) r (a k x),
        cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U))
      ∂Measure.pi (μ k) ∂P k) atTop
      (𝓝 (∫ x, ∫ y, F (spectralBlockView (m + 1) r x, y)
        ∂multivariateGaussian 0
          (cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x))
        ∂(Q₀ : Measure (SpectralArray (m + 1))))) := by
  sorry

end InvariantIsing

end

end OAI
end
