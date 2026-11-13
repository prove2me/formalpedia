-- Prove2me | Theorems.Thm_OAI_IsingPerceptron_random_countable_cylinder_insertion
-- name    : OAI.IsingPerceptron.random_countable_cylinder_insertion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:57:37.85168+00:00
-- url     : https://prove2.me/theorems/de0e8d09-bf3b-48a4-a7a2-426dec79e4f0
-- title:
--   OAI.IsingPerceptron.random_countable_cylinder_insertion: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.IsingPerceptron.random_countable_cylinder_insertion` of [lean/OAI/Probability/IsingPerceptron/NormalizedRestrictionPi.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/IsingPerceptron/NormalizedRestrictionPi.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.IsingPerceptron`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction`):
--
--   ```lean
--   theorem random_countable_cylinder_insertion {Ω X : Type*}
--       [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
--       {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
--       (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
--       (a b : X → ℕ →₀ ℝ) {K L : ℝ}
--       (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
--       (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
--       {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
--       (∫ ω, ∫ g, referenceReplicaMean (ν ω) (fun x => cylinderField (a x) g)
--         (fun σ => cylinderField (b (σ 0)) g*D σ) ∂gaussianCoordinates ∂P) =
--       (∫ ω, ∫ g, referenceReplicaMean (ν ω) (fun x => cylinderField (a x) g)
--         (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) ∂gaussianCoordinates ∂P) -
--       (r+1 : ℕ)*(∫ ω, ∫ g, referenceReplicaMean (ν ω) (fun x => cylinderField (a x) g)
--         (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
--         ∂gaussianCoordinates ∂P)
--   ```
--
--   **Definitions.** The statement is written with `OAI.IsingPerceptron.cylinderCross`, `OAI.IsingPerceptron.cylinderField`, `OAI.IsingPerceptron.gaussianCoordinates` and `OAI.IsingPerceptron.referenceReplicaMean` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.spinPriorFlat_leafPrefix_mean` and `OAI.InvariantIsing.tensorFlat_leafPrefix_mean` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/IsingPerceptron/NormalizedRestrictionPi.lean (declaration OAI.IsingPerceptron.random_countable_cylinder_insertion)

import Mathlib
import Definitions.Def_OAIQ4Ip000

section

attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

theorem random_countable_cylinder_insertion {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    (∫ ω, ∫ g, referenceReplicaMean (ν ω) (fun x => cylinderField (a x) g)
      (fun σ => cylinderField (b (σ 0)) g*D σ) ∂gaussianCoordinates ∂P) =
    (∫ ω, ∫ g, referenceReplicaMean (ν ω) (fun x => cylinderField (a x) g)
      (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) ∂gaussianCoordinates ∂P) -
    (r+1 : ℕ)*(∫ ω, ∫ g, referenceReplicaMean (ν ω) (fun x => cylinderField (a x) g)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
      ∂gaussianCoordinates ∂P) := by
  sorry

end IsingPerceptron

end

end OAI
end
