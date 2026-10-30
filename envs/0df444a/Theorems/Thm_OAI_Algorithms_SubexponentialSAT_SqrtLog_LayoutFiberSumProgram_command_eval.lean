-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutFiberSumProgram_command_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.command_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:08:36.262867+00:00
-- url     : https://prove2.me/theorems/71118b05-5662-4e2f-9521-68acfdf68dd3
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.command_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.command_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutFiberSumProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutFiberSumProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram`):
--
--   ```lean
--   theorem command_eval (entry : Code) (base : Data) (hb : Ready base)
--       (query : ℕ) (ps : List (ℕ × ℕ))
--       (hs : base.stacks 201=LayoutOwnerFiberProgram.stream ps)
--       (value : ℕ → ℤ) (T B M J : ℕ)
--       (hentry : ∀ i∈LayoutOwnerFiberProgram.fiberIndices query 0 ps,
--         EntryAt entry (parked base query) value T B M i)
--       (hJ : ∀ i∈LayoutOwnerFiberProgram.fiberIndices query 0 ps, i ≤ J)
--       (regs : Fin 16 → Bool) :
--       ∃ n < budget T B J query ps, ∃ rf result,
--         Eval (command entry) n (data base regs [] (unary query) ([],[]) ([],[]))
--           (data base rf [] (unary query) ([],[]) result) ∧
--         pairValue result=((LayoutOwnerFiberProgram.fiberIndices query 0 ps).map value).sum ∧
--         pairLength result ≤ (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*(B+2) ∧
--         pairTotal result.1 result.2 ≤ (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*M
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.fiberIndices` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.unary` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairTotal` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairValue` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.Code` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairLength` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.command` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.stream` (definitions bundle `OAIQ081S072` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.Data` (definitions bundle `OAIQ081S087` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.EntryAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.parked` (definitions bundle `OAIQ081S106` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.nativeEntryContract` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutFiberSumProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.command_eval)

import Mathlib
import Definitions.Def_OAIQ081S106

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

theorem command_eval (entry : Code) (base : Data) (hb : Ready base)
    (query : ℕ) (ps : List (ℕ × ℕ))
    (hs : base.stacks 201=LayoutOwnerFiberProgram.stream ps)
    (value : ℕ → ℤ) (T B M J : ℕ)
    (hentry : ∀ i∈LayoutOwnerFiberProgram.fiberIndices query 0 ps,
      EntryAt entry (parked base query) value T B M i)
    (hJ : ∀ i∈LayoutOwnerFiberProgram.fiberIndices query 0 ps, i ≤ J)
    (regs : Fin 16 → Bool) :
    ∃ n < budget T B J query ps, ∃ rf result,
      Eval (command entry) n (data base regs [] (unary query) ([],[]) ([],[]))
        (data base rf [] (unary query) ([],[]) result) ∧
      pairValue result=((LayoutOwnerFiberProgram.fiberIndices query 0 ps).map value).sum ∧
      pairLength result ≤ (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*(B+2) ∧
      pairTotal result.1 result.2 ≤ (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*M := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end
