-- Prove2me | Theorems.Thm_OAI_InvariantIsing_tensorPerturbation_minimizers_have_GG_limit
-- name    : OAI.InvariantIsing.tensorPerturbation_minimizers_have_GG_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:45:52.903122+00:00
-- url     : https://prove2.me/theorems/3eebecd2-60cd-4123-911b-3214afed58fe
-- title:
--   OAI.InvariantIsing.tensorPerturbation_minimizers_have_GG_limit: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.tensorPerturbation_minimizers_have_GG_limit` of [lean/OAI/Probability/InvariantIsing/Arrays/TensorLimitExistence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorLimitExistence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem tensorPerturbation_minimizers_have_GG_limit
--       (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
--       (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop)
--       (m n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
--       (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
--       (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
--       (eig c : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0 < K)
--       (heig : ∀ k i, |eig k i| ≤ K)
--       (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
--       (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, u k j ∈ Set.Icc (1 : ℝ) 2)
--       (v : ℕ → Fin m → ℝ) (hv : ∀ k a, v k a ∈ Set.Icc (1 : ℝ) 2)
--       (t : ℕ → ℝ) (ht : ∀ k, |t k| ≤ 1)
--       (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
--       (H : ℝ) (hH : ∀ k, h k n ≤ H)
--       (hmin : ∀ k u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
--         tensorPerturbationObjective (μ k) (eig k) (c k) (I k) (t k) n b (h k) (u k) (v k) ≤
--           tensorPerturbationObjective (μ k) (eig k) (c k) (I k) (t k) n b (h k) u' v') :
--       ∃ Q : ProbabilityMeasure (SpectralArray (m + 1)),
--         ∃ q : Fin (m + 1) → Set.Icc (0 : ℝ) 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
--         Tendsto (fun k => tensorPerturbedArrayLaw (μ (φ k)) (eig (φ k)) (c (φ k)) (I (φ k))
--           (u (φ k)) (v (φ k)) (t (φ k)) n b (h (φ k))) atTop (nhds Q) ∧
--         Tendsto (fun k => tensorMinimumArrayDiagonal (N (φ k)) n (v (φ k))) atTop (nhds q) ∧
--         HasEntryGhirlandaGuerra (fun x i j => x (i, j)) (Q : Measure (SpectralArray (m + 1))) ∧
--         (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i, i) a : ℝ) = q a)
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.GaussianLipschitzVarianceInput`, `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.SpectralArray` and `OAI.InvariantIsing.SpectralEntry` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.tensorMinimumArrayDiagonal` (definitions bundle `OAIQ258002` of this split); `OAI.InvariantIsing.HaarConcentrationInput` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.tensorPerturbationObjective` and `OAI.InvariantIsing.tensorPerturbedArrayLaw` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.CascadeExponents` and `OAI.IsingPerceptron.HasEntryGhirlandaGuerra` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proof of `OAI.InvariantIsing.tensorContact_no_positive_minimizing_sequence` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorLimitExistence.lean (declaration OAI.InvariantIsing.tensorPerturbation_minimizers_have_GG_limit)

import Mathlib
import Mathlib.MeasureTheory.Measure.Prokhorov
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorPerturbation_minimizers_have_GG_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop)
    (m n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0 < K)
    (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, u k j ∈ Set.Icc (1 : ℝ) 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, v k a ∈ Set.Icc (1 : ℝ) 2)
    (t : ℕ → ℝ) (ht : ∀ k, |t k| ≤ 1)
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (H : ℝ) (hH : ∀ k, h k n ≤ H)
    (hmin : ∀ k u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective (μ k) (eig k) (c k) (I k) (t k) n b (h k) (u k) (v k) ≤
        tensorPerturbationObjective (μ k) (eig k) (c k) (I k) (t k) n b (h k) u' v') :
    ∃ Q : ProbabilityMeasure (SpectralArray (m + 1)),
      ∃ q : Fin (m + 1) → Set.Icc (0 : ℝ) 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => tensorPerturbedArrayLaw (μ (φ k)) (eig (φ k)) (c (φ k)) (I (φ k))
        (u (φ k)) (v (φ k)) (t (φ k)) n b (h (φ k))) atTop (nhds Q) ∧
      Tendsto (fun k => tensorMinimumArrayDiagonal (N (φ k)) n (v (φ k))) atTop (nhds q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i, j)) (Q : Measure (SpectralArray (m + 1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i, i) a : ℝ) = q a) := by
  sorry

end InvariantIsing

end

end OAI
end
