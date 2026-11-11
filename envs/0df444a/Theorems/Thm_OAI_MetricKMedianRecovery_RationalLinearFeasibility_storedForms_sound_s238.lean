-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_RationalLinearFeasibility_storedForms_sound_s238
-- name    : OAI.MetricKMedianRecovery.RationalLinearFeasibility.storedForms_sound_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:30:39.44205+00:00
-- url     : https://prove2.me/theorems/43e97c09-b400-4653-9ed8-b19261bebcb7
-- title:
--   OAI.MetricKMedianRecovery.RationalLinearFeasibility.storedForms_sound_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.RationalLinearFeasibility.storedForms_sound` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/StoredForms.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/StoredForms.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.RationalLinearFeasibility`, with `open scoped BigOperators`):
--
--   ```lean
--   lemma storedForms_sound_s238 (e : Fin n ≃ V) (rows : List R) (f : R → Form V) (B : ℕ)
--       (x : V → ℚ) (hx : storedForms e rows f B=some x) :
--       (∀ r∈rows,(f r).eval x≤0) ∧ (∀ j,|x j|≤(B:ℚ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Form` and `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Form.eval` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.RationalLinearFeasibility.storedForms` (definitions bundle `Q238K022` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.continuation_spec_s238`, `OAI_MetricKMedianRecovery_EffectiveOpenability_storedOpening_none_iff_s238`, `OAI.MetricKMedianRecovery.RationalPhase.complete_spec_s238`, `OAI.MetricKMedianRecovery.RationalPhase.completion_spec_s238` and `OAI.MetricKMedianRecovery.RationalPhase.first_none_maximal_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/StoredForms.lean (declaration OAI.MetricKMedianRecovery.RationalLinearFeasibility.storedForms_sound)

import Mathlib
import Definitions.Def_Q238K022

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility
open scoped BigOperators
variable {V R : Type*} [Fintype V] {n : ℕ}

lemma storedForms_sound_s238 (e : Fin n ≃ V) (rows : List R) (f : R → Form V) (B : ℕ)
    (x : V → ℚ) (hx : storedForms e rows f B=some x) :
    (∀ r∈rows,(f r).eval x≤0) ∧ (∀ j,|x j|≤(B:ℚ)) := by
  sorry

end MetricKMedianRecovery.RationalLinearFeasibility

end OAI
end
