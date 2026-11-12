-- Prove2me | Theorems.Thm_OAI_InvariantIsing_tensorLeafGaussianMean_abs_sub_le
-- name    : OAI.InvariantIsing.tensorLeafGaussianMean_abs_sub_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:58:03.264428+00:00
-- url     : https://prove2.me/theorems/8279ee28-ed45-4b84-80bb-875ed338609c
-- title:
--   OAI.InvariantIsing.tensorLeafGaussianMean_abs_sub_le: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.tensorLeafGaussianMean_abs_sub_le` of [lean/OAI/Probability/InvariantIsing/Arrays/TensorGaussianMean.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorGaussianMean.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped BigOperators NNReal`):
--
--   ```lean
--   theorem tensorLeafGaussianMean_abs_sub_le {N m k : ℕ} (hN : 0 < N)
--       (U V : SpecialOrthogonal N) (I : Fin m → Finset (Fin N))
--       (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) (n : ℕ)
--       (site : Fin (n + 1) → ℝ≥0) (monomial : Fin (n + 1) → Fin k → ℝ≥0)
--       (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
--       (H : Spin N × LabeledLeaf n → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν) :
--       let A := fun R => tensorLeafCoefficients (specialRotation R) I degree amplitude n
--         (fun i => tensorVarianceProfile I degree (site i) (monomial i))
--       |(∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A U x) g) ∂ν)
--           ∂gaussianCoordinates) -
--         ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A V x) g) ∂ν)
--           ∂gaussianCoordinates| ≤
--         2 * (∑ i : Fin (n + 1), ∑ j, (monomial i j : ℝ) * amplitude j ^ 2 *
--           ∑ a, (degree j a : ℝ)) * frobeniusDistance U V
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.frobeniusDistance` and `OAI.InvariantIsing.specialRotation` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.tensorLeafCoefficients` and `OAI.InvariantIsing.tensorVarianceProfile` (definitions bundle `OAIQ258003` of this split); `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.cylinderField`, `OAI.IsingPerceptron.gaussianCoordinates` and `OAI.IsingPerceptron.labeledLeafMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.haar_tensorEnrichedPressure_variance`, `OAI.InvariantIsing.spinPriorMeanPressure_field` and `OAI.InvariantIsing.spinPriorProfileLog_variance` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/TensorGaussianMean.lean (declaration OAI.InvariantIsing.tensorLeafGaussianMean_abs_sub_le)

import Mathlib
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

theorem tensorLeafGaussianMean_abs_sub_le {N m k : ℕ} (hN : 0 < N)
    (U V : SpecialOrthogonal N) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) (n : ℕ)
    (site : Fin (n + 1) → ℝ≥0) (monomial : Fin (n + 1) → Fin k → ℝ≥0)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (H : Spin N × LabeledLeaf n → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν) :
    let A := fun R => tensorLeafCoefficients (specialRotation R) I degree amplitude n
      (fun i => tensorVarianceProfile I degree (site i) (monomial i))
    |(∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A U x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A V x) g) ∂ν)
        ∂gaussianCoordinates| ≤
      2 * (∑ i : Fin (n + 1), ∑ j, (monomial i j : ℝ) * amplitude j ^ 2 *
        ∑ a, (degree j a : ℝ)) * frobeniusDistance U V := by
  sorry

end InvariantIsing

end

end OAI
end
