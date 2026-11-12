-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBoundedDecision_run_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:36:23.42943+00:00
-- url     : https://prove2.me/theorems/1940067d-d0a8-4a46-b008-01dd0f25991e
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/BoundedDecision.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/BoundedDecision.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision`, with `open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid`, `open WordList RationalMatrix`):
--
--   ```lean
--   lemma run_pack_s238r {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
--       run (pack A b B)=[boundedIntegerDecide A b B]
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Ellipsoid.boundedIntegerDecide` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run` (definitions bundle `Q238L022` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.pack` (definitions bundle `Q238L024` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/BoundedDecision.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack)

import Mathlib
import Definitions.Def_Q238L022
import Definitions.Def_Q238L024

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

namespace BinaryBoundedDecision
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList RationalMatrix

lemma run_pack_s238r {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    run (pack A b B)=[boundedIntegerDecide A b B] := by
  sorry
end BinaryBoundedDecision

open WordOperations
end MetricKMedianRecovery.BitMachine

end OAI
end
