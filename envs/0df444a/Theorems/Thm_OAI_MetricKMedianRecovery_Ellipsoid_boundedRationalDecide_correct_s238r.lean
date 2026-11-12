-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_boundedRationalDecide_correct_s238r
-- name    : OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide_correct_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:27:07.698941+00:00
-- url     : https://prove2.me/theorems/f1635118-2c16-457e-a36d-95948bdfca77
-- title:
--   OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide_correct_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide_correct` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/DataHeight.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/DataHeight.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Ellipsoid`, with `open Matrix PolytopeCertificate RationalLinearFeasibility`, `open scoped BigOperators`):
--
--   ```lean
--   theorem boundedRationalDecide_correct_s238r {n : ℕ} (rows : List (Row n)) (B : ℕ) :
--       boundedRationalDecide rows B=true ↔
--         ∃ x : Fin n → ℝ, (∀ q∈rows, q.RealHolds x) ∧ (∀ j, |x j|≤(B:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row.RealHolds` (definitions bundle `Q238L010` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238r`, `OAI.MetricKMedianRecovery.EffectiveOpenability.storedOpening_complete_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.Stored.exactSolve_eq_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.selectFace_spec_s238r` and `OAI.MetricKMedianRecovery.RationalLinearFeasibility.storedForms_sound_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/DataHeight.lean (declaration OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide_correct)

import Mathlib
import Definitions.Def_Q238L009
import Definitions.Def_Q238L010

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

theorem boundedRationalDecide_correct_s238r {n : ℕ} (rows : List (Row n)) (B : ℕ) :
    boundedRationalDecide rows B=true ↔
      ∃ x : Fin n → ℝ, (∀ q∈rows, q.RealHolds x) ∧ (∀ j, |x j|≤(B:ℝ)) := by
  sorry

end MetricKMedianRecovery.Ellipsoid

end OAI
end
