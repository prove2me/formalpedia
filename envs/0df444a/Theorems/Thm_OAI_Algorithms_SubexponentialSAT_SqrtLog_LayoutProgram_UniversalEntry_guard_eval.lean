-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_UniversalEntry_guard_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry.guard_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:26:45.555885+00:00
-- url     : https://prove2.me/theorems/76436b30-40fc-43f8-843b-9598887477c2
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry.guard_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry.guard_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramUniversalEntry.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramUniversalEntry.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp`, `open SubexponentialSAT.MulticolorTypes`):
--
--   ```lean
--   theorem guard_eval (t : Fin Q) (u y : UniversalType r Q 1) (a : Data)
--       (ha : projectState id guardPorts a = Guard.guardInput (0 : Fin 1) t u y
--         [] [] [] [] a.regs) :
--       ∃ n ≤ MatrixExtendedEntryProgram.guardStageCost r Q 1 0 t.val+1,
--         ∃ e : Data, Eval guard n a e ∧ e.stacks=a.stacks ∧
--         e.regs 9=decide (MatrixExtendedEntryProgram.anchorValid (0 : Fin 1) t u y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry.guardPorts` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.anchorValid` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.guardStageCost` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Guard.guardInput` (definitions bundle `OAIQ081S073` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry.guard` (definitions bundle `OAIQ081S123` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry.Data` (definitions bundle `OAIQ081S157` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.command_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.command_eval` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramUniversalEntry.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry.guard_eval)

import Mathlib
import Definitions.Def_OAIQ081S157

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.MulticolorTypes

variable {r Q : ℕ}

theorem guard_eval (t : Fin Q) (u y : UniversalType r Q 1) (a : Data)
    (ha : projectState id guardPorts a = Guard.guardInput (0 : Fin 1) t u y
      [] [] [] [] a.regs) :
    ∃ n ≤ MatrixExtendedEntryProgram.guardStageCost r Q 1 0 t.val+1,
      ∃ e : Data, Eval guard n a e ∧ e.stacks=a.stacks ∧
      e.regs 9=decide (MatrixExtendedEntryProgram.anchorValid (0 : Fin 1) t u y) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry

end OAI.Algorithms
end
