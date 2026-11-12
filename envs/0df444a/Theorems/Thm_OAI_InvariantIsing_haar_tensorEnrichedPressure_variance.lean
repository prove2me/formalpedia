-- Prove2me | Theorems.Thm_OAI_InvariantIsing_haar_tensorEnrichedPressure_variance
-- name    : OAI.InvariantIsing.haar_tensorEnrichedPressure_variance
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:39:11.029839+00:00
-- url     : https://prove2.me/theorems/7bb5d94b-2a95-4600-bbee-e96810735481
-- title:
--   OAI.InvariantIsing.haar_tensorEnrichedPressure_variance: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.haar_tensorEnrichedPressure_variance` of [lean/OAI/Probability/InvariantIsing/Arrays/NSpinTensorHaar.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/NSpinTensorHaar.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped BigOperators NNReal`):
--
--   ```lean
--   theorem haar_tensorEnrichedPressure_variance (hpub : HaarConcentrationInput) :
--       ∃ C : ℝ, 0 < C ∧
--       ∀ N : ℕ, 3 ≤ N →
--       ∀ μ : Measure (SpecialOrthogonal N),
--         IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
--       ∀ m k : ℕ, ∀ eig c : Fin N → ℝ,
--       ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
--       ∀ I : Fin m → Finset (Fin N), ∀ degree : Fin k → Fin m → ℕ,
--       ∀ amplitude : Fin k → ℝ, ∀ n : ℕ, ∀ b : ℕ → ℝ,
--         CascadeExponents n b →
--       ∀ site : ℕ → ℝ≥0, ∀ monomial : ℕ → Fin k → ℝ≥0,
--         let v := fun i => tensorVarianceProfile I degree (site i) (monomial i)
--         let F := fun U : SpecialOrthogonal N =>
--           tensorEnrichedPressure eig (specialRotation U) c I degree amplitude n b
--             (fun i => v (i + 1)) (v 0)
--         let L := K + 2 * (N : ℝ)⁻¹ *
--           (∑ i : Fin (n + 1), ∑ j, (monomial i j : ℝ) * amplitude j ^ 2 * ∑ a, (degree j a : ℝ))
--         MemLp F 2 μ ∧ variance F μ ≤ C * L ^ 2 / N
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` and `OAI.InvariantIsing.SpinTensorIndex` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.SpecialOrthogonal` and `OAI.InvariantIsing.specialRotation` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.HaarConcentrationInput` and `OAI.InvariantIsing.tensorVarianceProfile` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.tensorEnrichedPressure` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.CascadeExponents` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.fullPerturbationPressure_variance`, `OAI.InvariantIsing.tensorNamespacedMeanPressure_perturbation_cost` and `OAI.InvariantIsing.tensorPerturbationPressureMean_modulus` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/NSpinTensorHaar.lean (declaration OAI.InvariantIsing.haar_tensorEnrichedPressure_variance)

import Mathlib
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

theorem haar_tensorEnrichedPressure_variance (hpub : HaarConcentrationInput) :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N),
      IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m k : ℕ, ∀ eig c : Fin N → ℝ,
    ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
    ∀ I : Fin m → Finset (Fin N), ∀ degree : Fin k → Fin m → ℕ,
    ∀ amplitude : Fin k → ℝ, ∀ n : ℕ, ∀ b : ℕ → ℝ,
      CascadeExponents n b →
    ∀ site : ℕ → ℝ≥0, ∀ monomial : ℕ → Fin k → ℝ≥0,
      let v := fun i => tensorVarianceProfile I degree (site i) (monomial i)
      let F := fun U : SpecialOrthogonal N =>
        tensorEnrichedPressure eig (specialRotation U) c I degree amplitude n b
          (fun i => v (i + 1)) (v 0)
      let L := K + 2 * (N : ℝ)⁻¹ *
        (∑ i : Fin (n + 1), ∑ j, (monomial i j : ℝ) * amplitude j ^ 2 * ∑ a, (degree j a : ℝ))
      MemLp F 2 μ ∧ variance F μ ≤ C * L ^ 2 / N := by
  sorry

end InvariantIsing

end

end OAI
end
