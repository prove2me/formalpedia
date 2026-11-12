-- Prove2me | Theorems.Thm_OAI_IsingPerceptron_cascadeEnergyLog_total_mean
-- name    : OAI.IsingPerceptron.cascadeEnergyLog_total_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:12:35.026062+00:00
-- url     : https://prove2.me/theorems/e32225e8-4b75-4a52-9c7a-ff7ccedd0f87
-- title:
--   OAI.IsingPerceptron.cascadeEnergyLog_total_mean: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.IsingPerceptron.cascadeEnergyLog_total_mean` of [lean/OAI/Probability/IsingPerceptron/VarianceOfConditionalCenterBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/IsingPerceptron/VarianceOfConditionalCenterBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.IsingPerceptron`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction`):
--
--   ```lean
--   lemma cascadeEnergyLog_total_mean {Ω : Type*} {I : Type} [MeasurableSpace Ω] [Fintype I]
--       [MeasurableSpace I] [MeasurableSingletonClass I] (P : Measure Ω) [IsProbabilityMeasure P]
--       (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
--       (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
--       (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
--       {H : Ω → I → ℝ} (hH : Measurable H) (hL : MemLp (fun ω => energyRecursion n b μ ν (H ω)) 2 P) :
--       (∫ p : Ω × NoiseTree (I → ℝ) n, cascadeEnergyLog n b μ ν (H p.1) p.2
--         ∂P.prod (noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n))) =
--         ∫ ω, energyRecursion n b μ ν (H ω) ∂P
--   ```
--
--   **Definitions.** The statement is written with `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.ExponentialNormMoments`, `OAI.IsingPerceptron.NoiseTree`, `OAI.IsingPerceptron.cascadeEnergyLog`, `OAI.IsingPerceptron.energyRecursion`, `OAI.IsingPerceptron.noiseCascadeLaw` and `OAI.IsingPerceptron.noiseTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proof of `OAI.InvariantIsing.magneticGroupValue_parameters_uniform` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/IsingPerceptron/VarianceOfConditionalCenterBound.lean (declaration OAI.IsingPerceptron.cascadeEnergyLog_total_mean)

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
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma cascadeEnergyLog_total_mean {Ω : Type*} {I : Type} [MeasurableSpace Ω] [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
    {H : Ω → I → ℝ} (hH : Measurable H) (hL : MemLp (fun ω => energyRecursion n b μ ν (H ω)) 2 P) :
    (∫ p : Ω × NoiseTree (I → ℝ) n, cascadeEnergyLog n b μ ν (H p.1) p.2
      ∂P.prod (noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n))) =
      ∫ ω, energyRecursion n b μ ν (H ω) ∂P := by
  sorry

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end
