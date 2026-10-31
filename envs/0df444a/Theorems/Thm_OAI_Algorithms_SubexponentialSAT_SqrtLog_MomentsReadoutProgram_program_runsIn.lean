-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsReadoutProgram_program_runsIn
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.program_runsIn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:53:19.302633+00:00
-- url     : https://prove2.me/theorems/9b867a27-0a12-4059-bcce-3403c58172a5
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.program_runsIn: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.program_runsIn` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsReadoutProgramNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsReadoutProgramNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`):
--
--   ```lean
--   theorem program_runsIn {n d : ℕ} (p e : ℕ) [Fact p.Prime]
--       (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
--       (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
--       (zero : RingProgram.Code (Word (baseWidth p e)) d)
--       (regs : Fin 8 → Bool) (width count t J shape : List Bool)
--       (hc : count.length=d) (hw : width.length=baseWidth p e) (hs : shape.length=n) :
--       let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
--       let bits := outputBits p e M cache entries t.length zero 0 J.length
--       ∃ rr, RunsIn program (readoutBudget (baseWidth p e) d n t.length J.length encoded+1)
--         ((wideState regs (MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [])
--           (inputHigh (RingProgram.flat zero) t J shape)).withPC (some program.entry))
--         ((wideState rr {MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [] with out:=bits}
--           (inputHigh (RingProgram.flat zero) t J shape)).withPC none)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Index` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.encodeDictionary` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.Tape` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.encodeIndex` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.readoutBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.inputTape` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.wideState` (definitions bundle `OAIQ081S127` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.outputBits` (definitions bundle `OAIQ081S130` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.inputHigh` (definitions bundle `OAIQ081S159` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.command` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.program` (definitions bundle `OAIQ081S169` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsReadoutProgramNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.program_runsIn)

import Mathlib
import Definitions.Def_OAIQ081S169

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem program_runsIn {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (zero : RingProgram.Code (Word (baseWidth p e)) d)
    (regs : Fin 8 → Bool) (width count t J shape : List Bool)
    (hc : count.length=d) (hw : width.length=baseWidth p e) (hs : shape.length=n) :
    let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
    let bits := outputBits p e M cache entries t.length zero 0 J.length
    ∃ rr, RunsIn program (readoutBudget (baseWidth p e) d n t.length J.length encoded+1)
      ((wideState regs (MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [])
        (inputHigh (RingProgram.flat zero) t J shape)).withPC (some program.entry))
      ((wideState rr {MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [] with out:=bits}
        (inputHigh (RingProgram.flat zero) t J shape)).withPC none) := by
  sorry

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
end
