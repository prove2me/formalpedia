-- Prove2me | Theorems.Thm_OAI_InvariantIsing_constrainedFieldValue_magneticBias
-- name    : OAI.InvariantIsing.constrainedFieldValue_magneticBias
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:36:55.725209+00:00
-- url     : https://prove2.me/theorems/38caae70-5dd3-40e1-9dda-22c023788ce1
-- title:
--   OAI.InvariantIsing.constrainedFieldValue_magneticBias: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.constrainedFieldValue_magneticBias` of [lean/OAI/Probability/InvariantIsing/Magnetic/MagneticFieldInverse.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/MagneticFieldInverse.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter`, `open scoped Topology`):
--
--   ```lean
--   lemma constrainedFieldValue_magneticBias (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
--       constrainedFieldValue h s = fieldValue h (magneticBias h s) - magneticBias h s * s
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.magneticBias` (definitions bundle `OAIQ258005` of this split); `OAI.InvariantIsing.FieldStep`, `OAI.InvariantIsing.constrainedFieldValue` and `OAI.InvariantIsing.fieldValue` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.finiteMagneticFunctional_ne_top_bot`, `OAI.InvariantIsing.finite_physical_field_pressure_upper`, `OAI.InvariantIsing.magneticBlockPath_l1_tendsto`, `OAI.InvariantIsing.magnetic_affine_increment_eventually_lower` and `OAI.InvariantIsing.magnetic_entropy_trial_eventually_lower` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/MagneticFieldInverse.lean (declaration OAI.InvariantIsing.constrainedFieldValue_magneticBias)

import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
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
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

lemma constrainedFieldValue_magneticBias (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    constrainedFieldValue h s = fieldValue h (magneticBias h s) - magneticBias h s * s := by
  sorry

end InvariantIsing

end

end OAI
end
