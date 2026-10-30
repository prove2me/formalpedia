-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_graphCountTail_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCountTail_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:46:16.894243+00:00
-- url     : https://prove2.me/theorems/f52b30ab-b9c3-47da-83fd-002003c9251e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCountTail_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCountTail_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramGraphCountTail.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramGraphCountTail.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open StructuredProgram (Atom)`):
--
--   ```lean
--   theorem graphCountTail_eval (ys xs : List (Bool × Bool)) (base : ScanState)
--       (hy : base.stacks 8 = framedCellStream ys)
--       (hx : base.stacks 12 = framedCellStream xs)
--       (h9 : base.stacks 9 = []) (h10 : base.stacks 10 = []) :
--       ∃ (n : ℕ) (next : ScanState), n + 1 ≤ 10 * ys.length + 10 * xs.length + 9 ∧
--         Eval graphCountTail n base next ∧
--         next.regs 7 = decide (cellWeight xs ≠ 0) ∧
--         next.stacks 9 = List.replicate (cellWeight ys) true ∧
--         next.stacks 16 = base.stacks 16 ∧ next.stacks 17 = base.stacks 17
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.cellWeight` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.framedCellStream` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCountTail` (definitions bundle `OAIQ081S029` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.ScanState` (definitions bundle `OAIQ081S050` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCounts_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramGraphCountTail.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCountTail_eval)

import Mathlib
import Definitions.Def_OAIQ081S050

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open StructuredProgram (Atom)

theorem graphCountTail_eval (ys xs : List (Bool × Bool)) (base : ScanState)
    (hy : base.stacks 8 = framedCellStream ys)
    (hx : base.stacks 12 = framedCellStream xs)
    (h9 : base.stacks 9 = []) (h10 : base.stacks 10 = []) :
    ∃ (n : ℕ) (next : ScanState), n + 1 ≤ 10 * ys.length + 10 * xs.length + 9 ∧
      Eval graphCountTail n base next ∧
      next.regs 7 = decide (cellWeight xs ≠ 0) ∧
      next.stacks 9 = List.replicate (cellWeight ys) true ∧
      next.stacks 16 = base.stacks 16 ∧ next.stacks 17 = base.stacks 17 := by
  sorry

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end
