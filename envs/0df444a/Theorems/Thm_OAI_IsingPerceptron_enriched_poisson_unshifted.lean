-- Prove2me | Theorems.Thm_OAI_IsingPerceptron_enriched_poisson_unshifted
-- name    : OAI.IsingPerceptron.enriched_poisson_unshifted
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:12:14.241353+00:00
-- url     : https://prove2.me/theorems/1ce3982d-5513-47f9-8f6e-688da4cfa352
-- title:
--   OAI.IsingPerceptron.enriched_poisson_unshifted: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.IsingPerceptron.enriched_poisson_unshifted` of [lean/OAI/Probability/IsingPerceptron/VarianceOfConditionalCenterBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/IsingPerceptron/VarianceOfConditionalCenterBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.IsingPerceptron`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction`):
--
--   ```lean
--   lemma enriched_poisson_unshifted {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
--       (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
--       (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
--       (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
--       {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
--       {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
--       (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
--       let μ := fun i => enrichedIncrementLaw N n h u (i+1)
--       let Q := ((poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
--         (Measure.infinitePi (fun _ : ℕ => P)))).prod
--           (noiseCascadeLaw (Spin N → ℝ) n b μ : Measure (NoiseTree (Spin N → ℝ) n))
--       let X := fun p : EnrichedPoissonRoot N A × NoiseTree (Spin N → ℝ) n =>
--         cascadeEnergyLog n b μ ν (enrichedPoissonBase n h u φ p.1) p.2
--       MemLp X 2 Q ∧ Var[X;Q] ≤
--         4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
--         +N*h 0+4*N*(perturbationScale N)^2+5*K^2*r
--   ```
--
--   **Definitions.** The statement is written with `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.EnrichedPoissonRoot`, `OAI.IsingPerceptron.EnrichedRootSize`, `OAI.IsingPerceptron.NoiseTree`, `OAI.IsingPerceptron.RawTree`, `OAI.IsingPerceptron.Spin`, `OAI.IsingPerceptron.cascadeEnergyLog`, `OAI.IsingPerceptron.enrichedIncrementLaw`, `OAI.IsingPerceptron.enrichedPoissonBase`, `OAI.IsingPerceptron.noiseCascadeLaw`, `OAI.IsingPerceptron.noiseTreeMeasurableSpace`, `OAI.IsingPerceptron.perturbationScale`, `OAI.IsingPerceptron.rawCascadeLaw`, `OAI.IsingPerceptron.rawTreeMeasurableSpace` and `OAI.IsingPerceptron.rawTreeTotal` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.magneticGroupValue_parameters_uniform` and `OAI.IsingPerceptron.enrichedMeanPressure_field_insert` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/IsingPerceptron/VarianceOfConditionalCenterBound.lean (declaration OAI.IsingPerceptron.enriched_poisson_unshifted)

import Mathlib
import Definitions.Def_OAIQ4Ip000

section

attribute [-instance] _root_.OAI.IsingPerceptron.enrichedCoordinateLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.spinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma enriched_poisson_unshifted {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    let μ := fun i => enrichedIncrementLaw N n h u (i+1)
    let Q := ((poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))).prod
        (noiseCascadeLaw (Spin N → ℝ) n b μ : Measure (NoiseTree (Spin N → ℝ) n))
    let X := fun p : EnrichedPoissonRoot N A × NoiseTree (Spin N → ℝ) n =>
      cascadeEnergyLog n b μ ν (enrichedPoissonBase n h u φ p.1) p.2
    MemLp X 2 Q ∧ Var[X;Q] ≤
      4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
      +N*h 0+4*N*(perturbationScale N)^2+5*K^2*r := by
  sorry

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end
