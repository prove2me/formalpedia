-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_localStep_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.localStep_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:24:19.226534+00:00
-- url     : https://prove2.me/theorems/3a245567-807f-402e-b878-e9fc4d62cbb1
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.localStep_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.localStep_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramLocal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramLocal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic`):
--
--   ```lean
--   theorem localStep_eval {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
--       (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
--       (a : Fin t) (b : ℕ) (qt st : List Bool) (ready : LocalReady base D m b side v)
--       (i : ℕ) (hi : i < D) (d : Data) (inv : LocalInvariant (m:=m) base shifts Q side v a b qt st i d) :
--       ∃ n e, n ≤ 2000*(portWidth base+D+1)^2 ∧ Eval portStep n d e ∧
--         e.stacks portLoop.counter=d.stacks portLoop.counter ∧
--         LocalInvariant (m:=m) base shifts Q side v a b qt st (i+1) e
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.UnaryForPrograms.Ports` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.Cube` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.F3` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Data` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.LocalInvariant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.LocalReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portStep` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portWidth` (definitions bundle `OAIQ081S118` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.rowStep_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgramLocal.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.localStep_eval)

import Mathlib
import Definitions.Def_OAIQ081S118

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem localStep_eval {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (b : ℕ) (qt st : List Bool) (ready : LocalReady base D m b side v)
    (i : ℕ) (hi : i < D) (d : Data) (inv : LocalInvariant (m:=m) base shifts Q side v a b qt st i d) :
    ∃ n e, n ≤ 2000*(portWidth base+D+1)^2 ∧ Eval portStep n d e ∧
      e.stacks portLoop.counter=d.stacks portLoop.counter ∧
      LocalInvariant (m:=m) base shifts Q side v a b qt st (i+1) e := by
  sorry

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end
