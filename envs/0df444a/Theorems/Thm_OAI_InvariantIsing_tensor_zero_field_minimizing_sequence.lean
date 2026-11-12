-- Prove2me | Theorems.Thm_OAI_InvariantIsing_tensor_zero_field_minimizing_sequence
-- name    : OAI.InvariantIsing.tensor_zero_field_minimizing_sequence
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:46:35.374195+00:00
-- url     : https://prove2.me/theorems/8d6a76d5-5eaa-48b3-9a28-26c8e58b471c
-- title:
--   OAI.InvariantIsing.tensor_zero_field_minimizing_sequence: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.tensor_zero_field_minimizing_sequence` of [lean/OAI/Probability/InvariantIsing/Arrays/TensorMinimumSequence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorMinimumSequence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`):
--
--   ```lean
--   theorem tensor_zero_field_minimizing_sequence
--       (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
--       (m depth : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents depth b)
--       (μ : (N : ℕ) → Measure (SpecialOrthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
--       (hμ : ∀ N, (μ N).IsMulLeftInvariant)
--       (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N)) :
--       ∃ u : (N : ℕ) → Fin N → ℝ, ∃ v : ℕ → Fin m → ℝ,
--         (∀ N j, u N j ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ N a, v N a ∈ Set.Icc (1 : ℝ) 2) ∧
--         ∀ N, 3≤N → ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
--           (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
--           tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b
--             (fun _ => 0) (u N) (v N) ≤
--           tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b (fun _ => 0) u' v'
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.GaussianLipschitzVarianceInput` and `OAI.InvariantIsing.SpecialOrthogonal` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.HaarConcentrationInput` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.tensorPerturbationObjective` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.CascadeExponents` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.CompactSpectralPartition.pressure_tendsto` and `OAI.InvariantIsing.CompactSpectralPartition.selected_pressure_tendsto` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorMinimumSequence.lean (declaration OAI.InvariantIsing.tensor_zero_field_minimizing_sequence)

import Mathlib
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem tensor_zero_field_minimizing_sequence
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (m depth : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    (hμ : ∀ N, (μ N).IsMulLeftInvariant)
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N)) :
    ∃ u : (N : ℕ) → Fin N → ℝ, ∃ v : ℕ → Fin m → ℝ,
      (∀ N j, u N j ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ N a, v N a ∈ Set.Icc (1 : ℝ) 2) ∧
      ∀ N, 3≤N → ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
        (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
        tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b
          (fun _ => 0) (u N) (v N) ≤
        tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b (fun _ => 0) u' v' := by
  sorry

end InvariantIsing

end

end OAI
end
