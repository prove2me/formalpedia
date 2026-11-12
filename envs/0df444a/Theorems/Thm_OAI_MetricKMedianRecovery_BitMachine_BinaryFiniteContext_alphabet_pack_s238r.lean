-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_alphabet_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.alphabet_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:49:00.701879+00:00
-- url     : https://prove2.me/theorems/0cf4965a-1179-41aa-9ea6-7e35f982a8be
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.alphabet_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.alphabet_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/FiniteContext.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/FiniteContext.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext`, with `open Classical`, `open WordOperations WordList BinaryOpeningPayment RationalLeaves`, `open BinaryLabel (orderedSort)`):
--
--   ```lean
--   lemma alphabet_pack_s238r {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
--       (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
--       alphabet (pack distance loc F Q v z lam)=labels (FiniteLabelContinuation.alphabet loc F Q)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.FiniteLabelContinuation.alphabet` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.labels` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder` (definitions bundle `Q238L019` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.alphabet` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack` (definitions bundle `Q238L029` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.advanceInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.c_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.crossInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.finishInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.step_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.selected_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.history_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.chosen_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryScan.nodes_pack_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/FiniteContext.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.alphabet_pack)

import Mathlib
import Definitions.Def_Q238L029

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open Classical
open WordOperations WordList BinaryOpeningPayment RationalLeaves
open BinaryLabel (orderedSort)

lemma alphabet_pack_s238r {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    alphabet (pack distance loc F Q v z lam)=labels (FiniteLabelContinuation.alphabet loc F Q) := by
  sorry

attribute [local irreducible] BinaryLabelMatrix.run
attribute [local irreducible] matrix selected
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end
