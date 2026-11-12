-- Prove2me | Theorems.Thm_OAI_InvariantIsing_continuous_cavitySynchronizedBlock
-- name    : OAI.InvariantIsing.continuous_cavitySynchronizedBlock
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:16:04.358705+00:00
-- url     : https://prove2.me/theorems/9398fc1d-090d-4077-bcd8-cba59e5f8b36
-- title:
--   OAI.InvariantIsing.continuous_cavitySynchronizedBlock: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.continuous_cavitySynchronizedBlock` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityCascadeSpectralLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityCascadeSpectralLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set`, `open scoped Topology BoundedContinuousFunction`):
--
--   ```lean
--   lemma continuous_cavitySynchronizedBlock {m r : ℕ} (d : SpectralEntry m)
--       (f : Fin m → ℝ → Icc (-1 : ℝ) 1) (hf : ∀ a, Continuous (f a)) :
--       Continuous (cavitySynchronizedBlock (r := r) d f)
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.SpectralBlock`, `OAI.InvariantIsing.SpectralEntry` and `OAI.InvariantIsing.cavitySynchronizedBlock` (definitions bundle `OAIQ258001` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_canonical_group_block_tendsto`, `OAI.InvariantIsing.cavity_finite_cascade_block_average`, `OAI.InvariantIsing.cavity_finite_model_numerator`, `OAI.InvariantIsing.cavity_haar_gibbs_numerator_match`, `OAI.InvariantIsing.cavity_haar_restricted_gibbs_regularized_match`, `OAI.InvariantIsing.cavity_haar_strict_restricted_spin_match` and `OAI.InvariantIsing.cavity_strict_recalculated_gaussian_error` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityCascadeSpectralLimit.lean (declaration OAI.InvariantIsing.continuous_cavitySynchronizedBlock)

import Mathlib
import Definitions.Def_OAIQ258001

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

lemma continuous_cavitySynchronizedBlock {m r : ℕ} (d : SpectralEntry m)
    (f : Fin m → ℝ → Icc (-1 : ℝ) 1) (hf : ∀ a, Continuous (f a)) :
    Continuous (cavitySynchronizedBlock (r := r) d f) := by
  sorry

end InvariantIsing

end

end OAI
end
