-- Prove2me | Theorems.Thm_OAI_InvariantIsing_field_support_equal_cutList
-- name    : OAI.InvariantIsing.field_support_equal_cutList
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:37:18.3122+00:00
-- url     : https://prove2.me/theorems/c2191dab-3138-4d06-a931-f86cc8bbfe73
-- title:
--   OAI.InvariantIsing.field_support_equal_cutList: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.field_support_equal_cutList` of [lean/OAI/Probability/InvariantIsing/Fields/FieldPartitionSupport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/FieldPartitionSupport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory IsingPerceptron Set`, `open scoped BigOperators NNReal`):
--
--   ```lean
--   lemma field_support_equal_cutList {h k : FieldStep}
--       (he : List.ofFn h.cut = List.ofFn k.cut) :
--       fieldValue k 0 ≤ fieldValue h 0 - (1 / 2 : ℝ) *
--         ∫ s, fieldMagnetizationPath h s * (fieldFunction k s - fieldFunction h s) ∂pathMeasure
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.fieldMagnetizationPath` (definitions bundle `OAIQ258005` of this split); `OAI.InvariantIsing.FieldStep`, `OAI.InvariantIsing.fieldFunction`, `OAI.InvariantIsing.fieldValue`, `OAI.InvariantIsing.pathMeasure` and `OAI.InvariantIsing.OverlapPath` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.cavity_window_minimum_variational_lower` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/FieldPartitionSupport.lean (declaration OAI.InvariantIsing.field_support_equal_cutList)

import Mathlib
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Fin.InsertNth
import Mathlib.Probability.Distributions.Gaussian.Real
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
open MeasureTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

lemma field_support_equal_cutList {h k : FieldStep}
    (he : List.ofFn h.cut = List.ofFn k.cut) :
    fieldValue k 0 ≤ fieldValue h 0 - (1 / 2 : ℝ) *
      ∫ s, fieldMagnetizationPath h s * (fieldFunction k s - fieldFunction h s) ∂pathMeasure := by
  sorry

end InvariantIsing

end

end OAI
end
