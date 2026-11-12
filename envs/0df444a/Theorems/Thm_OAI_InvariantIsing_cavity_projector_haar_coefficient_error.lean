-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_projector_haar_coefficient_error
-- name    : OAI.InvariantIsing.cavity_projector_haar_coefficient_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:24:03.174894+00:00
-- url     : https://prove2.me/theorems/9fdbe68b-41be-4f30-878c-8905434e7625
-- title:
--   OAI.InvariantIsing.cavity_projector_haar_coefficient_error: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_projector_haar_coefficient_error` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityProjectorHaarMean.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityProjectorHaarMean.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter`, `open scoped Topology Matrix`):
--
--   ```lean
--   lemma cavity_projector_haar_coefficient_error {N n m d depth : ℕ}
--       (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
--       (a₀ : Fin d → Fin m) (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν]
--       (T : LabeledTree depth) (lam v : Fin m → ℝ)
--       (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ) {D : ℝ} (hD : 0 ≤ D)
--       (A A' : CavityFactorBlocks d n)
--       (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
--       {M s : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) (hs : 0 < s) :
--       |(∫ V, cavityProjectorCavityMean T
--         (fun a => t*lam a+2*perturbationScale N*v a) u t D A F
--         (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν) -
--         ∫ V, cavityProjectorCavityMean T
--         (fun a => t*lam a+2*perturbationScale N*v a) u t D A' F
--         (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν| ≤
--         4*|t| *D*cavityFactorDeviation A A'/s+M^2*s/2
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` and `OAI.InvariantIsing.CavityFactorBlocks` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.cavityCanonicalProjectorFrame`, `OAI.InvariantIsing.cavityFactorDeviation`, `OAI.InvariantIsing.cavityLabeledProjectorAction` and `OAI.InvariantIsing.cavityProjectorCavityMean` (definitions bundle `OAIQ258003` of this split); `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.LabeledTree` and `OAI.IsingPerceptron.perturbationScale` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Orthogonal` and `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.cavity_haar_cutoff_limit_family` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityProjectorHaarMean.lean (declaration OAI.InvariantIsing.cavity_projector_haar_coefficient_error)

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

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Matrix

namespace InvariantIsing

lemma cavity_projector_haar_coefficient_error {N n m d depth : ℕ}
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν]
    (T : LabeledTree depth) (lam v : Fin m → ℝ)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ) {D : ℝ} (hD : 0 ≤ D)
    (A A' : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    {M s : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) (hs : 0 < s) :
    |(∫ V, cavityProjectorCavityMean T
      (fun a => t*lam a+2*perturbationScale N*v a) u t D A F
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν) -
      ∫ V, cavityProjectorCavityMean T
      (fun a => t*lam a+2*perturbationScale N*v a) u t D A' F
      (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν| ≤
      4*|t| *D*cavityFactorDeviation A A'/s+M^2*s/2 := by
  sorry

end InvariantIsing

end

end OAI
end
