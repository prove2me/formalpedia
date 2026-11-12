-- Prove2me | Theorems.Thm_OAI_IsingPerceptron_enrichedCoordinatePressure_eq_noise
-- name    : OAI.IsingPerceptron.enrichedCoordinatePressure_eq_noise
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:12:19.595632+00:00
-- url     : https://prove2.me/theorems/bd75a6a0-7c18-4432-a26c-a83ce099b412
-- title:
--   OAI.IsingPerceptron.enrichedCoordinatePressure_eq_noise: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.IsingPerceptron.enrichedCoordinatePressure_eq_noise` of [lean/OAI/Probability/IsingPerceptron/EnergyShift.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/IsingPerceptron/EnergyShift.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.IsingPerceptron`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal`):
--
--   ```lean
--   theorem enrichedCoordinatePressure_eq_noise {N : ℕ} {A : Type*} [MeasurableSpace A]
--       (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
--       (hb : CascadeExponents n b) (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
--       {φ : A → Spin N → ℝ} (hm : Measurable φ) :
--       enrichedCoordinatePressure n h u ν φ =ᵐ[enrichedCoordinateLaw P r N n b]
--         (fun p => enrichedPoissonLog n b h u ν φ (enrichedToNoise n h u p) / N)
--   ```
--
--   **Definitions.** The statement is written with `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.EnrichedLabeledData`, `OAI.IsingPerceptron.EnrichedPoissonRoot`, `OAI.IsingPerceptron.EnrichedRootSize`, `OAI.IsingPerceptron.ForestVertex`, `OAI.IsingPerceptron.InfiniteRootData`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.Spin`, `OAI.IsingPerceptron.enrichedCoordinateLaw`, `OAI.IsingPerceptron.enrichedCoordinatePressure`, `OAI.IsingPerceptron.enrichedPoissonLog`, `OAI.IsingPerceptron.enrichedToNoise` and `OAI.IsingPerceptron.labeledTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.magneticGroupValue_parameters_uniform` and `OAI.IsingPerceptron.enrichedMeanPressure_field_insert` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/IsingPerceptron/EnergyShift.lean (declaration OAI.IsingPerceptron.enrichedCoordinatePressure_eq_noise)

import Mathlib
import Definitions.Def_OAIQ4Ip000

section

attribute [-instance] _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.IsingPerceptron.spinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

theorem enrichedCoordinatePressure_eq_noise {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (hb : CascadeExponents n b) (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) :
    enrichedCoordinatePressure n h u ν φ =ᵐ[enrichedCoordinateLaw P r N n b]
      (fun p => enrichedPoissonLog n b h u ν φ (enrichedToNoise n h u p) / N) := by
  sorry

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end
