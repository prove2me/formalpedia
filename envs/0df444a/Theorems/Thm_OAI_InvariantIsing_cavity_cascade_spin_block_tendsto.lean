-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_cascade_spin_block_tendsto
-- name    : OAI.InvariantIsing.cavity_cascade_spin_block_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:10:35.010992+00:00
-- url     : https://prove2.me/theorems/6c19d6b8-3624-4a05-bfad-7e8227c513da
-- title:
--   OAI.InvariantIsing.cavity_cascade_spin_block_tendsto: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_cascade_spin_block_tendsto` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityCascadeBlockLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityCascadeBlockLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set`, `open scoped Topology BoundedContinuousFunction`):
--
--   ```lean
--   theorem cavity_cascade_spin_block_tendsto
--       {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
--       (B : Ω → RealArray) (hB : Measurable B)
--       (hGG : HasGhirlandaGuerra B μ)
--       (hG : ∀ᵐ x ∂μ, GramDiagonal 1 (B x))
--       (hU : ∀ᵐ x ∂μ, IsUltrametricArray (B x))
--       (q : ℝ → ℝ) (hq : Monotone q) (hb : ∀ u, q u ∈ Icc (0 : ℝ) 1)
--       (hp : μ.map (fun x => B x 0 1) = unitUniform.map q)
--       (r : ℕ) (F : (Fin r → Fin r → ℝ) →ᵇ ℝ) :
--       Tendsto (fun n => ∫ x, F (arrayBlock spinArray r x)
--         ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage q n) : Measure JointArray))
--         atTop (𝓝 (∫ x, F (arrayBlock B r x) ∂μ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.IsingPerceptron.GramDiagonal`, `OAI.IsingPerceptron.HasGhirlandaGuerra`, `OAI.IsingPerceptron.IsUltrametricArray`, `OAI.IsingPerceptron.JointArray`, `OAI.IsingPerceptron.JointEntry`, `OAI.IsingPerceptron.RealArray`, `OAI.IsingPerceptron.arrayBlock`, `OAI.IsingPerceptron.cascadeCompactLaw`, `OAI.IsingPerceptron.spinArray`, `OAI.IsingPerceptron.uniformCellAverage`, `OAI.IsingPerceptron.uniformExponent` and `OAI.IsingPerceptron.unitUniform` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proof of `OAI.InvariantIsing.cavity_canonical_group_block_tendsto` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityCascadeBlockLimit.lean (declaration OAI.InvariantIsing.cavity_cascade_spin_block_tendsto)

import Mathlib
import Definitions.Def_OAIQ4Ip000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_cascade_spin_block_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Ω → RealArray) (hB : Measurable B)
    (hGG : HasGhirlandaGuerra B μ)
    (hG : ∀ᵐ x ∂μ, GramDiagonal 1 (B x))
    (hU : ∀ᵐ x ∂μ, IsUltrametricArray (B x))
    (q : ℝ → ℝ) (hq : Monotone q) (hb : ∀ u, q u ∈ Icc (0 : ℝ) 1)
    (hp : μ.map (fun x => B x 0 1) = unitUniform.map q)
    (r : ℕ) (F : (Fin r → Fin r → ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, F (arrayBlock spinArray r x)
      ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage q n) : Measure JointArray))
      atTop (𝓝 (∫ x, F (arrayBlock B r x) ∂μ)) := by
  sorry

end InvariantIsing

end

end OAI
end
