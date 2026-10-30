-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_graphWordCallback_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordCallback_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:06:26.254778+00:00
-- url     : https://prove2.me/theorems/1b66907c-d46f-4264-8e48-2b5b9a2bc28b
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordCallback_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordCallback_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramGraphCallback.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramGraphCallback.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage`, `open StructuredProgram (Atom)`):
--
--   ```lean
--   theorem graphWordCallback_eval {D r : ℕ} (s : Fin D → Cayley.Cube r)
--       (x : Cayley.Cube r) (q : ℕ) (qbits Dbits : List Bool)
--       (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
--       (a : GraphSearchState) (he : GraphWorkEmpty a)
--       (hm : a.stacks 29 = matrixFrames s) (ht : a.stacks 30 = List.replicate D true)
--       (hq : a.stacks 31 = qbits) (hD : a.stacks 32 = Dbits) (htmp : a.stacks 35 = [])
--       (hx : a.stacks 34 = (scalarFrames (List.ofFn x)).reverse) :
--       ∃ (n : ℕ) (out : GraphSearchState), n ≤ graphCallbackBudget D r qbits.length Dbits.length ∧
--         Eval graphWordCallback n a out ∧ GraphWorkEmpty out ∧
--         out.regs 15 = decide (graphWordRejects s x q) ∧
--         out.regs 13 = a.regs 13 ∧ out.regs 14 = a.regs 14 ∧ out.stacks 34 = [] ∧
--         (∀ i : Fin 36, 29 ≤ i.val → i ≠ 34 → out.stacks i = a.stacks i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.Cube` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCallbackBudget` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordRejects` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects` (definitions bundle `OAIQ081S029` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.scalarFrames` (definitions bundle `OAIQ081S050` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.GraphSearchState` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordCallback` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.GraphWorkEmpty` (definitions bundle `OAIQ081S102` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_stream_runs` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramGraphCallback.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordCallback_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S102

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open StructuredProgram (Atom)

theorem graphWordCallback_eval {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (x : Cayley.Cube r) (q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (a : GraphSearchState) (he : GraphWorkEmpty a)
    (hm : a.stacks 29 = matrixFrames s) (ht : a.stacks 30 = List.replicate D true)
    (hq : a.stacks 31 = qbits) (hD : a.stacks 32 = Dbits) (htmp : a.stacks 35 = [])
    (hx : a.stacks 34 = (scalarFrames (List.ofFn x)).reverse) :
    ∃ (n : ℕ) (out : GraphSearchState), n ≤ graphCallbackBudget D r qbits.length Dbits.length ∧
      Eval graphWordCallback n a out ∧ GraphWorkEmpty out ∧
      out.regs 15 = decide (graphWordRejects s x q) ∧
      out.regs 13 = a.regs 13 ∧ out.regs 14 = a.regs 14 ∧ out.stacks 34 = [] ∧
      (∀ i : Fin 36, 29 ≤ i.val → i ≠ 34 → out.stacks i = a.stacks i) := by
  sorry

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end
