-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_physical_projector_increment
-- name    : OAI.InvariantIsing.cavity_physical_projector_increment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:22:57.928197+00:00
-- url     : https://prove2.me/theorems/9d2de121-e354-496b-a660-3a8a28e11354
-- title:
--   OAI.InvariantIsing.cavity_physical_projector_increment: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_physical_projector_increment` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityPhysicalProjectorIncrement.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityPhysicalProjectorIncrement.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped Matrix`):
--
--   ```lean
--   theorem cavity_physical_projector_increment {N n m d depth : ℕ} (hN : 0 < N)
--       (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
--       (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
--       (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
--       (es : Fin (m*n) ≃ Fin (d+n))
--       (U : SpecialOrthogonal (N+n)) (lam : Fin m → ℝ) (a₀ : Fin d → Fin m)
--       (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
--       (hB : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
--         B (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 1)
--       (hBT : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
--         cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
--       (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
--       (T : LabeledTree depth) (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
--       (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t cap : ℝ) (hcap : 0 ≤ cap) :
--       let G := cavityCompressionGrams g (cavitySpecialOrthogonal U)
--       let A := cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam)
--         (Matrix.diagonal (fun j => lam (a₀ j))) (B G) (cavitySpectralStack G)
--       let p := cavityPhysicalLabeledProjectors g B a₀ (cavitySpecialOrthogonal U)
--       let c := fun a => t*lam a+2*perturbationScale N*v a
--       let δ := cavityDeterministicRate n m (2*(2*n+1)) N +
--         2*cavityCovarianceRate n (2*n+1) N
--       cavityProjectorCappedLog T c u t cap δ A p + cavityProjectorLogPartition T c u p.1 ≤
--         ∫ z, Real.log (∫ x, Real.exp
--           (cavityRotationHamiltonian (specialRotation U)
--             (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
--             (cavitySpectralGroup g) u z x)
--           ∂labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
--           ∂gaussianCoordinates
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.CavityFactorBlocks` and `OAI.InvariantIsing.CavityProjectorFrame` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.cavityCompressionGrams`, `OAI.InvariantIsing.cavityCovarianceRate`, `OAI.InvariantIsing.cavityDeterministicRate`, `OAI.InvariantIsing.cavityRepeatedSpectrum`, `OAI.InvariantIsing.cavitySpecialOrthogonal`, `OAI.InvariantIsing.cavitySpectralGroup`, `OAI.InvariantIsing.cavitySpectralStack`, `OAI.InvariantIsing.diagonalPerturbedEigenvalues` and `OAI.InvariantIsing.specialRotation` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityPhysicalLabeledProjectors`, `OAI.InvariantIsing.cavityProjectorCappedLog`, `OAI.InvariantIsing.cavityProjectorLogPartition`, `OAI.InvariantIsing.cavityRotationHamiltonian`, `OAI.InvariantIsing.cavitySmallFactorBlocks` and `OAI.InvariantIsing.uniformSpinPrior` (definitions bundle `OAIQ258003` of this split); `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.gaussianCoordinates`, `OAI.IsingPerceptron.labeledLeafMeasurableSpace`, `OAI.IsingPerceptron.labeledSpinReference` and `OAI.IsingPerceptron.perturbationScale` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.cavity_tree_pressure_capped_increment` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityPhysicalProjectorIncrement.lean (declaration OAI.InvariantIsing.cavity_physical_projector_increment)

import Mathlib
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.StrongLaw
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem cavity_physical_projector_increment {N n m d depth : ℕ} (hN : 0 < N)
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n))
    (U : SpecialOrthogonal (N+n)) (lam : Fin m → ℝ) (a₀ : Fin d → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      B (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 1)
    (hBT : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (T : LabeledTree depth) (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t cap : ℝ) (hcap : 0 ≤ cap) :
    let G := cavityCompressionGrams g (cavitySpecialOrthogonal U)
    let A := cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam)
      (Matrix.diagonal (fun j => lam (a₀ j))) (B G) (cavitySpectralStack G)
    let p := cavityPhysicalLabeledProjectors g B a₀ (cavitySpecialOrthogonal U)
    let c := fun a => t*lam a+2*perturbationScale N*v a
    let δ := cavityDeterministicRate n m (2*(2*n+1)) N +
      2*cavityCovarianceRate n (2*n+1) N
    cavityProjectorCappedLog T c u t cap δ A p + cavityProjectorLogPartition T c u p.1 ≤
      ∫ z, Real.log (∫ x, Real.exp
        (cavityRotationHamiltonian (specialRotation U)
          (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
          (cavitySpectralGroup g) u z x)
        ∂labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
        ∂gaussianCoordinates := by
  sorry

end InvariantIsing

end

end OAI
end
