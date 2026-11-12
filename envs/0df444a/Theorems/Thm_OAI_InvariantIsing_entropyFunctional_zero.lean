-- Prove2me | Theorems.Thm_OAI_InvariantIsing_entropyFunctional_zero
-- name    : OAI.InvariantIsing.entropyFunctional_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:26:13.444847+00:00
-- url     : https://prove2.me/theorems/05d1f3b3-1164-4477-a11d-dba0a73ce7aa
-- title:
--   OAI.InvariantIsing.entropyFunctional_zero: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.entropyFunctional_zero` of [lean/OAI/Probability/InvariantIsing/Fields/FieldBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/FieldBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory`, `open scoped BigOperators`):
--
--   ```lean
--   lemma entropyFunctional_zero : entropyFunctional (constantPath 0 (by constructor <;> norm_num)) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.constantPath` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.entropyFunctional` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.compact_spectral_field_pressure_tendsto_of_mem`, `OAI.InvariantIsing.compact_spectral_pressure_tendsto_of_mem`, `OAI.InvariantIsing.finiteMagneticVariational_ne_top_bot`, `OAI.InvariantIsing.finiteVariational_ne_top_bot`, `OAI.InvariantIsing.physical_mean_wasserstein_field_pressure_tendsto`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae`, `OAI.InvariantIsing.selected_spectral_pressure_tendsto` and `OAI.InvariantIsing.variationalFunctional_constant` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/FieldBounds.lean (declaration OAI.InvariantIsing.entropyFunctional_zero)

import Mathlib
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003

section

attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
attribute [-simp] _root_.OAI.InvariantIsing.fieldAllIncrements_length _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

lemma entropyFunctional_zero : entropyFunctional (constantPath 0 (by constructor <;> norm_num)) = 0 := by
  sorry

end InvariantIsing

end

end OAI
end
