-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_graphWord_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWord_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:58:35.423379+00:00
-- url     : https://prove2.me/theorems/ffd6003c-7efd-45a7-a2a7-3fba915ca4bc
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWord_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWord_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramGraphWord.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramGraphWord.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open StructuredProgram (Atom)`):
--
--   ```lean
--   theorem graphWord_eval {r D : ℕ} (s : Fin D → Cayley.Cube r)
--       (x : Cayley.Cube r) (q : ℕ) (qbits Dbits : List Bool)
--       (hq : BinaryArithmetic.toNat qbits = q) (hD : BinaryArithmetic.toNat Dbits = D)
--       (a : GraphWordState)
--       (hin : projectState graphCountRegisters graphCountStacks a =
--         extendPairState (matrixInput s x (a.regs ∘ graphCountRegisters)) qbits Dbits)
--       (hclean : ∀ i : Fin 29, 18 ≤ i.val → a.stacks i = []) :
--       ∃ (n : ℕ) (out : GraphWordState), n + 1 ≤ graphWordBudget D r qbits.length Dbits.length ∧
--         Eval graphWordCommand n a out ∧ out.regs 15 = decide (graphWordRejects s x q) ∧
--         out.stacks 16 = qbits ∧ out.stacks 17 = Dbits ∧
--         (∀ i : Fin 29, 18 ≤ i.val → out.stacks i = []) ∧
--         out.regs 13 = a.regs 13 ∧ out.regs 14 = a.regs 14
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.Cube` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCountRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCountStacks` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordBudget` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordRejects` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects` (definitions bundle `OAIQ081S029` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixInput` (definitions bundle `OAIQ081S050` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordCommand` (definitions bundle `OAIQ081S069` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.GraphWordState` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.extendPairState` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordCallback_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramGraphWord.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWord_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S084

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

theorem graphWord_eval {r D : ℕ} (s : Fin D → Cayley.Cube r)
    (x : Cayley.Cube r) (q : ℕ) (qbits Dbits : List Bool)
    (hq : BinaryArithmetic.toNat qbits = q) (hD : BinaryArithmetic.toNat Dbits = D)
    (a : GraphWordState)
    (hin : projectState graphCountRegisters graphCountStacks a =
      extendPairState (matrixInput s x (a.regs ∘ graphCountRegisters)) qbits Dbits)
    (hclean : ∀ i : Fin 29, 18 ≤ i.val → a.stacks i = []) :
    ∃ (n : ℕ) (out : GraphWordState), n + 1 ≤ graphWordBudget D r qbits.length Dbits.length ∧
      Eval graphWordCommand n a out ∧ out.regs 15 = decide (graphWordRejects s x q) ∧
      out.stacks 16 = qbits ∧ out.stacks 17 = Dbits ∧
      (∀ i : Fin 29, 18 ≤ i.val → out.stacks i = []) ∧
      out.regs 13 = a.regs 13 ∧ out.regs 14 = a.regs 14 := by
  sorry

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end
