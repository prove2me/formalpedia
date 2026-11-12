-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteMachine_completed_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:07:06.326993+00:00
-- url     : https://prove2.me/theorems/b3755f8c-99de-44bb-b97e-a3f92649f155
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/FiniteMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/FiniteMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine`, with `open WordOperations WordList RationalLeaves`, `open BinaryOpeningPayment (field field_computes field_encode)`, `open BinaryFiniteContext (pack labels)`):
--
--   ```lean
--   lemma completed_pack_s238r {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
--       (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
--       completed (pack distance loc F Q v z lam)=BinaryOpeningActivity.indices
--         (RationalPhase.completion (FiniteLabelContinuation.rows loc F Q (rows distance))
--           (FiniteLabelContinuation.select loc F Q F) v z lam (FiniteLabelContinuation.select loc F Q Q))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.FiniteLabelContinuation.alphabet`, `OAI.MetricKMedianRecovery.FiniteLabelContinuation.rows` and `OAI.MetricKMedianRecovery.FiniteLabelContinuation.select` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder` (definitions bundle `Q238L019` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.rows`, `OAI.MetricKMedianRecovery.RationalPhase.completion` and `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.indices` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack` (definitions bundle `Q238L029` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed` (definitions bundle `Q238L039` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.step_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/FiniteMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed_pack)

import Mathlib
import Definitions.Def_Q238L039

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteMachine
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (pack labels)

lemma completed_pack_s238r {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    completed (pack distance loc F Q v z lam)=BinaryOpeningActivity.indices
      (RationalPhase.completion (FiniteLabelContinuation.rows loc F Q (rows distance))
        (FiniteLabelContinuation.select loc F Q F) v z lam (FiniteLabelContinuation.select loc F Q Q)) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

end OAI
end
