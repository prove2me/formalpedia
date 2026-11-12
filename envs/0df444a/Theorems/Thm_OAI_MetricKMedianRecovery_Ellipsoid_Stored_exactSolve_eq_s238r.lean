-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_Stored_exactSolve_eq_s238r
-- name    : OAI.MetricKMedianRecovery.Ellipsoid.Stored.exactSolve_eq_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:34:50.98089+00:00
-- url     : https://prove2.me/theorems/c50820f6-539d-4cce-8d5e-c165e7953432
-- title:
--   OAI.MetricKMedianRecovery.Ellipsoid.Stored.exactSolve_eq_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Ellipsoid.Stored.exactSolve_eq` of [lean/OAI/Combinatorics/KMedianRecovery/Encoding/Matrix.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/Matrix.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Ellipsoid.Stored`, with `open Matrix RationalLinearFeasibility`, `open scoped BigOperators`):
--
--   ```lean
--   @[simp] theorem exactSolve_eq_s238r {n : ℕ} (rows : List (Row n)) (B : ℕ) :
--       exactSolve rows B=Ellipsoid.exactSolve rows B
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.exactSolve` and `OAI.MetricKMedianRecovery.Ellipsoid.Stored.exactSolve` (definitions bundle `Q238L020` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238r`, `OAI.MetricKMedianRecovery.EffectiveOpenability.storedOpening_complete_s238r` and `OAI.MetricKMedianRecovery.RationalLinearFeasibility.storedForms_sound_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/Matrix.lean (declaration OAI.MetricKMedianRecovery.Ellipsoid.Stored.exactSolve_eq)

import Mathlib
import Definitions.Def_Q238L020

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid.Stored
open Matrix RationalLinearFeasibility
open scoped BigOperators

@[simp] theorem exactSolve_eq_s238r {n : ℕ} (rows : List (Row n)) (B : ℕ) :
    exactSolve rows B=Ellipsoid.exactSolve rows B := by
  sorry

end MetricKMedianRecovery.Ellipsoid.Stored

end OAI
end
