-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_DisjointBranchProgram_resultB_length_le
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.resultB_length_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:50:58.777798+00:00
-- url     : https://prove2.me/theorems/f793674e-7be4-46df-84f5-132ef940d98c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.resultB_length_le: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.resultB_length_le` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointSparsifyProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointSparsifyProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram`, with `open OAI.Algorithms.SubexponentialSAT.SAT`, `open BitProgram StructuredCalls`):
--
--   ```lean
--   theorem resultB_length_le (F S : List (List ℕ)) (H : List ℕ) :
--       (ExecCoreChildProgram.formulaCode (resultB SubexpFrontend.negateCode F S H)).length ≤
--         5 * ExecCoreChildProgram.inputVolume F S H
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpFrontend.negateCode` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.formulaCode` and `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.inputVolume` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.resultB` (definitions bundle `OAIQ081S064` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.branch_execution_from_state` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource.branch_execution_space` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointSparsifyProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.resultB_length_le)

import Mathlib
import Definitions.Def_OAIQ081S064

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram

open OAI.Algorithms.SubexponentialSAT.SAT

open BitProgram StructuredCalls

theorem resultB_length_le (F S : List (List ℕ)) (H : List ℕ) :
    (ExecCoreChildProgram.formulaCode (resultB SubexpFrontend.negateCode F S H)).length ≤
      5 * ExecCoreChildProgram.inputVolume F S H := by
  sorry

open ExecBranchControllerSupport

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram
end
