-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram_Specialization_raw_dictionary_runsIn
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization.raw_dictionary_runsIn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:18:54.064935+00:00
-- url     : https://prove2.me/theorems/171e677d-351d-4ebb-9b7e-ecd88f3660f6
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization.raw_dictionary_runsIn: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization.raw_dictionary_runsIn` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSpecializationProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSpecializationProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization`, with `open OAI BitProgram StructuredCalls`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog MomentsProjectionProgram`, `open Squarefree`):
--
--   ```lean
--   theorem raw_dictionary_runsIn {n : ℕ} (U : Finset (Fin n))
--       (l : List (Index (Fin n) × List Bool)) (regs : Fin 5 → Bool) :
--       ∃ rf, RunsIn program
--         (200*((Squarefree.Program.rawEntries (l.map fun a => (encodeIndex a.1,a.2))).length+1)*(n+2)+1)
--         ((machine regs {input:=Encoding.frame (encodeMask U)++
--           Squarefree.Program.rawEntries (l.map fun a => (encodeIndex a.1,a.2))}).withPC (some program.entry))
--         ((machine rf {target:=(encodeMask U).reverse,framed:=
--           Squarefree.Program.rawEntries ((HeadEvaluation.specializeEntries U l).map
--             fun a => (encodeIndex a.1,a.2))}).withPC none)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Index` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.ByteRecord` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.encodeMask` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.Tape` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.encodeIndex` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.rawEntries` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation.specializeEntries` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization.program` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization.project` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.machine` (definitions bundle `OAIQ081S109` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.frame` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.run_space` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSpecializationProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization.raw_dictionary_runsIn)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S109

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog MomentsProjectionProgram

open Squarefree

theorem raw_dictionary_runsIn {n : ℕ} (U : Finset (Fin n))
    (l : List (Index (Fin n) × List Bool)) (regs : Fin 5 → Bool) :
    ∃ rf, RunsIn program
      (200*((Squarefree.Program.rawEntries (l.map fun a => (encodeIndex a.1,a.2))).length+1)*(n+2)+1)
      ((machine regs {input:=Encoding.frame (encodeMask U)++
        Squarefree.Program.rawEntries (l.map fun a => (encodeIndex a.1,a.2))}).withPC (some program.entry))
      ((machine rf {target:=(encodeMask U).reverse,framed:=
        Squarefree.Program.rawEntries ((HeadEvaluation.specializeEntries U l).map
          fun a => (encodeIndex a.1,a.2))}).withPC none) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization
end
