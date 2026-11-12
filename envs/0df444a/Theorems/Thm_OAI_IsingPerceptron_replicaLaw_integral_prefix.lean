-- Prove2me | Theorems.Thm_OAI_IsingPerceptron_replicaLaw_integral_prefix
-- name    : OAI.IsingPerceptron.replicaLaw_integral_prefix
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:12:07.034877+00:00
-- url     : https://prove2.me/theorems/cd73169f-5535-4faf-8e5a-ac2d79ad28db
-- title:
--   OAI.IsingPerceptron.replicaLaw_integral_prefix: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.IsingPerceptron.replicaLaw_integral_prefix` of [lean/OAI/Probability/IsingPerceptron/TiltedLabelLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/IsingPerceptron/TiltedLabelLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.IsingPerceptron`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction`):
--
--   ```lean
--   lemma replicaLaw_integral_prefix {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
--       [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
--       (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
--       {r : ℕ} (D : (Fin r → X) → ℝ) {C : ℝ} (hD : ∀ σ, |D σ| ≤ C) :
--       (∫ σ, D (fun i : Fin r => σ i) ∂replicaLaw P ν hν) =
--         ∫ ω, ∫ σ, D σ ∂Measure.pi (fun _ : Fin r => ν ω) ∂P
--   ```
--
--   **Definitions.** The statement is written with `OAI.IsingPerceptron.replicaLaw` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_finite_cascade_block_average` and `OAI.InvariantIsing.cavity_haar_restricted_gibbs_regularized_match` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/IsingPerceptron/TiltedLabelLaw.lean (declaration OAI.IsingPerceptron.replicaLaw_integral_prefix)

import Mathlib
import Definitions.Def_OAIQ4Ip000

section

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

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma replicaLaw_integral_prefix {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {r : ℕ} (D : (Fin r → X) → ℝ) {C : ℝ} (hD : ∀ σ, |D σ| ≤ C) :
    (∫ σ, D (fun i : Fin r => σ i) ∂replicaLaw P ν hν) =
      ∫ ω, ∫ σ, D σ ∂Measure.pi (fun _ : Fin r => ν ω) ∂P := by
  sorry

end IsingPerceptron

end

end OAI
end
