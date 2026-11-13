-- Prove2me | Theorems.Thm_OAI_IsingPerceptron_enrichedMeanPressure_recursion
-- name    : OAI.IsingPerceptron.enrichedMeanPressure_recursion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:57:26.947339+00:00
-- url     : https://prove2.me/theorems/a17a83e4-625b-45ef-9567-a2eef1d98e24
-- title:
--   OAI.IsingPerceptron.enrichedMeanPressure_recursion: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.IsingPerceptron.enrichedMeanPressure_recursion` of [lean/OAI/Probability/IsingPerceptron/VariationalDefs.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/IsingPerceptron/VariationalDefs.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.IsingPerceptron`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped BigOperators Topology ENNReal`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal`):
--
--   ```lean
--   theorem enrichedMeanPressure_recursion {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
--       (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
--       (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
--       (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
--       {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
--       {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
--       (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
--       enrichedMeanPressure P r n b h u ν φ =
--         ((∫ p, energyRecursion n b (fun i => enrichedIncrementLaw N n h u (i+1)) ν
--             (enrichedPoissonBase n h u φ p)
--           ∂(poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
--             (Measure.infinitePi (fun _ : ℕ => P)))) - N*h n/2)/N
--   ```
--
--   **Definitions.** The statement is written with `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.EnrichedRootSize`, `OAI.IsingPerceptron.Spin`, `OAI.IsingPerceptron.energyRecursion`, `OAI.IsingPerceptron.enrichedIncrementLaw`, `OAI.IsingPerceptron.enrichedMeanPressure` and `OAI.IsingPerceptron.enrichedPoissonBase` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.constrainedFieldValue_magneticBias`, `OAI.InvariantIsing.fieldBiasMean_magneticBias`, `OAI.InvariantIsing.magneticBias_uniform_bound`, `OAI.InvariantIsing.magneticVariational_inward_mono` and `OAI.InvariantIsing.magnetic_entropy_sequence_of_support` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/IsingPerceptron/VariationalDefs.lean (declaration OAI.IsingPerceptron.enrichedMeanPressure_recursion)

import Mathlib
import Definitions.Def_OAIQ4Ip000

section

attribute [-instance] _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

theorem enrichedMeanPressure_recursion {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    enrichedMeanPressure P r n b h u ν φ =
      ((∫ p, energyRecursion n b (fun i => enrichedIncrementLaw N n h u (i+1)) ν
          (enrichedPoissonBase n h u φ p)
        ∂(poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
          (Measure.infinitePi (fun _ : ℕ => P)))) - N*h n/2)/N := by
  sorry

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end
