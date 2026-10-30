-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_preparedGraphWord_length_le
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.preparedGraphWord_length_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:06:43.35014+00:00
-- url     : https://prove2.me/theorems/52d6030f-0c88-4b22-907c-d06789d32b1f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.preparedGraphWord_length_le: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.preparedGraphWord_length_le` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramGraphBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramGraphBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp`):
--
--   ```lean
--   theorem preparedGraphWord_length_le {D r : ℕ} (s : Fin D → Cayley.Cube r)
--       (x : Cayley.Cube r) (qbits Dbits : List Bool) (a : GraphSearchState)
--       (he : GraphWorkEmpty a) (hm : a.stacks 29 = matrixFrames s)
--       (ht : a.stacks 30 = List.replicate D true) (hq : a.stacks 31 = qbits)
--       (hD : a.stacks 32 = Dbits) (hx : a.stacks 34 = (scalarFrames (List.ofFn x)).reverse)
--       (i : Fin 29) :
--       ((projectState id graphWordStacks (preparedGraphWord a)).stacks i).length ≤
--         graphInputSpan D r qbits.length Dbits.length
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.Cube` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphInputSpan` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordStacks` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.scalarFrames` (definitions bundle `OAIQ081S050` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.GraphSearchState` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.preparedGraphWord` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.GraphWorkEmpty` (definitions bundle `OAIQ081S102` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordCallback_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramGraphBounds.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.preparedGraphWord_length_le)

import Mathlib
import Definitions.Def_OAIQ081S102

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem preparedGraphWord_length_le {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (x : Cayley.Cube r) (qbits Dbits : List Bool) (a : GraphSearchState)
    (he : GraphWorkEmpty a) (hm : a.stacks 29 = matrixFrames s)
    (ht : a.stacks 30 = List.replicate D true) (hq : a.stacks 31 = qbits)
    (hD : a.stacks 32 = Dbits) (hx : a.stacks 34 = (scalarFrames (List.ofFn x)).reverse)
    (i : Fin 29) :
    ((projectState id graphWordStacks (preparedGraphWord a)).stacks i).length ≤
      graphInputSpan D r qbits.length Dbits.length := by
  sorry

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end
