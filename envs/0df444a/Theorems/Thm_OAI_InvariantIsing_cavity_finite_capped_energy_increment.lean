-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_finite_capped_energy_increment
-- name    : OAI.InvariantIsing.cavity_finite_capped_energy_increment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:20:14.613623+00:00
-- url     : https://prove2.me/theorems/75e61766-830f-4022-b251-ef14bb63c792
-- title:
--   OAI.InvariantIsing.cavity_finite_capped_energy_increment: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_finite_capped_energy_increment` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityFiniteCappedIncrement.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityFiniteCappedIncrement.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped BigOperators`):
--
--   ```lean
--   theorem cavity_finite_capped_energy_increment {N n m depth : ℕ} (hN : 0 < N)
--       (U : Rotation (N + n)) (V : Rotation N)
--       (I : Fin m → Finset (Fin (N + n))) (J : Fin m → Finset (Fin N))
--       (eig : Fin (N + n) → ℝ) (eig₀ : Fin N → ℝ)
--       (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
--       (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t cap : ℝ) (hcap : 0 ≤ cap)
--       (ν : Measure ((Spin N × Spin n) × LabeledLeaf depth)) [IsProbabilityMeasure ν]
--       (w : Spin N × Spin n → ℝ) (hw : ∀ x, 1 ≤ w x)
--       {C : ℝ} (hC : 0 ≤ C)
--       (herr : ∀ x y a, |projectedOverlap U (I a) (cavityJoinedSpin x) (cavityJoinedSpin y) -
--         projectedOverlap V (J a) x.1 y.1| ≤ C / N * (w x + w y)) :
--       let H := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
--         rotatedEnergy (diagonalPerturbedEigenvalues eig₀ J v t) V x.1.1
--       let W := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
--         t * (rotatedEnergy eig U (cavityJoinedSpin x.1) - rotatedEnergy eig₀ V x.1.1)
--       let F := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
--         rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U (cavityJoinedSpin x.1)
--       let A := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
--         cavityPerturbationCoefficients U I u depth (cavityJoinedSpin x.1, x.2)
--       let B := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
--         cavityPerturbationCoefficients V J u depth (x.1.1, x.2)
--       let δ := cavityDeterministicRate n m (2 * C) N + 2 * cavityCovarianceRate n C N
--       (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (min (W x) cap - δ * w x.1)
--         ∂ν.tilted (fun x => H x + cylinderField (B x) g)) ∂gaussianCoordinates) ≤
--         (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (F x + cylinderField (A x) g) ∂ν)
--           ∂gaussianCoordinates) -
--         ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (B x) g) ∂ν)
--           ∂gaussianCoordinates
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.cavityCovarianceRate`, `OAI.InvariantIsing.cavityDeterministicRate` and `OAI.InvariantIsing.diagonalPerturbedEigenvalues` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityJoinedSpin`, `OAI.InvariantIsing.cavityPerturbationCoefficients` and `OAI.InvariantIsing.projectedOverlap` (definitions bundle `OAIQ258003` of this split); `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.cylinderField`, `OAI.IsingPerceptron.gaussianCoordinates` and `OAI.IsingPerceptron.labeledLeafMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Rotation`, `OAI.InvariantIsing.Spin` and `OAI.InvariantIsing.rotatedEnergy` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_physical_projector_increment` and `OAI.InvariantIsing.restricted_physical_projector_increment` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityFiniteCappedIncrement.lean (declaration OAI.InvariantIsing.cavity_finite_capped_energy_increment)

import Mathlib
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem cavity_finite_capped_energy_increment {N n m depth : ℕ} (hN : 0 < N)
    (U : Rotation (N + n)) (V : Rotation N)
    (I : Fin m → Finset (Fin (N + n))) (J : Fin m → Finset (Fin N))
    (eig : Fin (N + n) → ℝ) (eig₀ : Fin N → ℝ)
    (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t cap : ℝ) (hcap : 0 ≤ cap)
    (ν : Measure ((Spin N × Spin n) × LabeledLeaf depth)) [IsProbabilityMeasure ν]
    (w : Spin N × Spin n → ℝ) (hw : ∀ x, 1 ≤ w x)
    {C : ℝ} (hC : 0 ≤ C)
    (herr : ∀ x y a, |projectedOverlap U (I a) (cavityJoinedSpin x) (cavityJoinedSpin y) -
      projectedOverlap V (J a) x.1 y.1| ≤ C / N * (w x + w y)) :
    let H := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      rotatedEnergy (diagonalPerturbedEigenvalues eig₀ J v t) V x.1.1
    let W := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      t * (rotatedEnergy eig U (cavityJoinedSpin x.1) - rotatedEnergy eig₀ V x.1.1)
    let F := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U (cavityJoinedSpin x.1)
    let A := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      cavityPerturbationCoefficients U I u depth (cavityJoinedSpin x.1, x.2)
    let B := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      cavityPerturbationCoefficients V J u depth (x.1.1, x.2)
    let δ := cavityDeterministicRate n m (2 * C) N + 2 * cavityCovarianceRate n C N
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (min (W x) cap - δ * w x.1)
      ∂ν.tilted (fun x => H x + cylinderField (B x) g)) ∂gaussianCoordinates) ≤
      (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (F x + cylinderField (A x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (B x) g) ∂ν)
        ∂gaussianCoordinates := by
  sorry

end InvariantIsing

end

end OAI
end
