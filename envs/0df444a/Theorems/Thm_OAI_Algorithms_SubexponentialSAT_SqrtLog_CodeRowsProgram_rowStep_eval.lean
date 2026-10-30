-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_rowStep_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.rowStep_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:26:03.806737+00:00
-- url     : https://prove2.me/theorems/444acc94-39ca-478a-bd4c-f47089ee6444
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.rowStep_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.rowStep_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramRow.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramRow.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic SubexponentialSAT.StackRoutines`):
--
--   ```lean
--   theorem rowStep_eval {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
--       (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
--       (a : Fin t) (b : ℕ) (qt : List Bool) (ready : LocalReady base D m b side v)
--       (hq : base.stacks 0=CodeSearchProgram.scalarFrames (List.ofFn (Q a))++qt)
--       (hs : base.stacks 9=shiftRows (List.ofFn shifts))
--       (hD : (base.stacks 6).length=D)
--       (h1 : base.stacks 1=[]) (h13 : base.stacks 13=[])
--       (h14 : base.stacks 14=[]) (h15 : base.stacks 15=[]) :
--       ∃ n rf, Eval rowStep n base
--         ⟨rf,rowStacks base qt (rowPayload b m (slots m shifts Q side v a))⟩ ∧
--         n ≤ rowCost base D b ∧ (∀ j : Fin 16, 12 ≤ j.val → rf j=base.regs j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.Cube` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.F3` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.rowPayload` (definitions bundle `OAIQ081S028` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.slots` (definitions bundle `OAIQ081S029` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.shiftRows` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.scalarFrames` (definitions bundle `OAIQ081S050` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Data` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.LocalReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.rowCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.rowStacks` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.rowStep` (definitions bundle `OAIQ081S118` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.checkLoop_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramRow.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.rowStep_eval)

import Mathlib
import Definitions.Def_OAIQ081S118

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic SubexponentialSAT.StackRoutines

theorem rowStep_eval {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (b : ℕ) (qt : List Bool) (ready : LocalReady base D m b side v)
    (hq : base.stacks 0=CodeSearchProgram.scalarFrames (List.ofFn (Q a))++qt)
    (hs : base.stacks 9=shiftRows (List.ofFn shifts))
    (hD : (base.stacks 6).length=D)
    (h1 : base.stacks 1=[]) (h13 : base.stacks 13=[])
    (h14 : base.stacks 14=[]) (h15 : base.stacks 15=[]) :
    ∃ n rf, Eval rowStep n base
      ⟨rf,rowStacks base qt (rowPayload b m (slots m shifts Q side v a))⟩ ∧
      n ≤ rowCost base D b ∧ (∀ j : Fin 16, 12 ≤ j.val → rf j=base.regs j) := by
  sorry

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end
