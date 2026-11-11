-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_boundedRationalDecide_correct_s238
-- name    : OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide_correct_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:20:04.421035+00:00
-- url     : https://prove2.me/theorems/bff05e67-ae4e-4934-8cac-0ebd682d7d1a
-- title:
--   OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide_correct_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide_correct` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/DataHeight.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/DataHeight.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Ellipsoid`, with `open Matrix PolytopeCertificate RationalLinearFeasibility`, `open scoped BigOperators`):
--
--   ```lean
--   theorem boundedRationalDecide_correct_s238 {n : ℕ} (rows : List (Row n)) (B : ℕ) :
--       boundedRationalDecide rows B=true ↔
--         ∃ x : Fin n → ℝ, (∀ q∈rows, q.RealHolds x) ∧ (∀ j, |x j|≤(B:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row.RealHolds` (definitions bundle `Q238K015` of this split).
--
--   **Used by.** The proofs of `OAI_MetricKMedianRecovery_BitMachine_BinaryExactSolve_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryRawOpening_run_pack_s238`, `OAI.MetricKMedianRecovery.EffectiveOpenability.storedOpening_complete_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.Stored.exactSolve_eq_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.selectFace_spec_s238`, `OAI_MetricKMedianRecovery_RationalLinearFeasibility_storedForms_complete_s238` and `OAI.MetricKMedianRecovery.RationalLinearFeasibility.storedForms_sound_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/DataHeight.lean (declaration OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide_correct)

import Mathlib
import Definitions.Def_Q238K014
import Definitions.Def_Q238K015

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix PolytopeCertificate RationalLinearFeasibility
open scoped BigOperators

theorem boundedRationalDecide_correct_s238 {n : ℕ} (rows : List (Row n)) (B : ℕ) :
    boundedRationalDecide rows B=true ↔
      ∃ x : Fin n → ℝ, (∀ q∈rows, q.RealHolds x) ∧ (∀ j, |x j|≤(B:ℝ)) := by
  sorry

end MetricKMedianRecovery.Ellipsoid

end OAI
end
