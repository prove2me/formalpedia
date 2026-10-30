-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_program_runsIn
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.program_runsIn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:25:18.175159+00:00
-- url     : https://prove2.me/theorems/e295145b-cac8-471a-90f7-f84fc7469a22
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.program_runsIn: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.program_runsIn` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic`):
--
--   ```lean
--   theorem program_runsIn {r D t m : ℕ} (regs : Fin 16 → Bool) (dword mword width : List Bool)
--       (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3)
--       (hd : BinaryArithmetic.toNat dword=D) (hm : BinaryArithmetic.toNat mword=m) (hcap : 3*m ≤ 2^width.length) :
--       ∃ rf, RunsIn program (cost dword mword width shifts Q)
--         ((inputState regs dword mword width shifts Q).withPC (some program.entry))
--         ((outputState (m:=m) rf dword mword width shifts Q).withPC none)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.Cube` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.F3` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.cost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.inputState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.outputState` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.program` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.afterMetadata_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeRowsProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.program_runsIn)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S118

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem program_runsIn {r D t m : ℕ} (regs : Fin 16 → Bool) (dword mword width : List Bool)
    (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3)
    (hd : BinaryArithmetic.toNat dword=D) (hm : BinaryArithmetic.toNat mword=m) (hcap : 3*m ≤ 2^width.length) :
    ∃ rf, RunsIn program (cost dword mword width shifts Q)
      ((inputState regs dword mword width shifts Q).withPC (some program.entry))
      ((outputState (m:=m) rf dword mword width shifts Q).withPC none) := by
  sorry

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end
