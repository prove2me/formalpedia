-- Prove2me | Theorems.Thm_OAI_InvariantIsing_field_vector_spin_pair_evaluation
-- name    : OAI.InvariantIsing.field_vector_spin_pair_evaluation
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:38:33.543325+00:00
-- url     : https://prove2.me/theorems/bbb823d0-cef4-4887-9209-912b2ec432f9
-- title:
--   OAI.InvariantIsing.field_vector_spin_pair_evaluation: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.field_vector_spin_pair_evaluation` of [lean/OAI/Probability/InvariantIsing/Fields/FieldSpinEvaluation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/FieldSpinEvaluation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`):
--
--   ```lean
--   theorem field_vector_spin_pair_evaluation (hpub : PanchenkoTalagrandFieldPairInput)
--       (N : ℕ) (hN : 0 < N) (h : FieldStep)
--       (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
--       {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
--       (∫ z, fieldVectorSpinPairMean N h z q Φ j
--         ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ))) =
--         ∫ s, Φ (q (fieldLevelIndex h s)) * fieldMagnetizationPath h s ∂pathMeasure
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.vectorGaussianLaw` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.fieldLevelIndex` (definitions bundle `OAIQ258002` of this split); `OAI.InvariantIsing.PanchenkoTalagrandFieldPairInput` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.fieldMagnetizationPath` and `OAI.InvariantIsing.fieldVectorSpinPairMean` (definitions bundle `OAIQ258005` of this split); `OAI.InvariantIsing.FieldStep`, `OAI.InvariantIsing.pathMeasure` and `OAI.InvariantIsing.OverlapPath` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.cavity_linear_rooted_spin_evaluation` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/FieldSpinEvaluation.lean (declaration OAI.InvariantIsing.field_vector_spin_pair_evaluation)

import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.Variance
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem field_vector_spin_pair_evaluation (hpub : PanchenkoTalagrandFieldPairInput)
    (N : ℕ) (hN : 0 < N) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    (∫ z, fieldVectorSpinPairMean N h z q Φ j
      ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ))) =
      ∫ s, Φ (q (fieldLevelIndex h s)) * fieldMagnetizationPath h s ∂pathMeasure := by
  sorry

end InvariantIsing

end

end OAI
end
