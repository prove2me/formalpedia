-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSProgram_branch_execution_from_state
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.branch_execution_from_state
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:15:12.554918+00:00
-- url     : https://prove2.me/theorems/3e7736c2-a988-453e-a406-94a2529331ef
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.branch_execution_from_state: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.branch_execution_from_state` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparseDFSProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparseDFSProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram`, with `open BitProgram StructuredCalls SubexpPostfixControl`):
--
--   ```lean
--   theorem branch_execution_from_state (d : Data) (F S : List (List ℕ)) (H : List ℕ)
--       (hF : d.stacks 265 = ExecCoreChildProgram.formulaCode F)
--       (hH : d.stacks 9 = ExecCoreChildProgram.clauseCode H)
--       (hS : d.stacks 12 = ExecCoreChildProgram.formulaCode S)
--       (hleft : d.stacks 261 = []) (hright : d.stacks 262 = [])
--       (hclean : ∀ i : Fin 1220, i.val < 24 → i ≠ 9 → i ≠ 12 → d.stacks i = []) :
--       ∃ t ≤ 621000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2,
--         ∃ e, Eval branch t d e ∧
--           e.stacks 257 =
--             ExecWorklistProgram.record
--               (ExecCoreChildProgram.formulaCode (ExecCoreChildProgram.result F S H)) ++
--             (ExecWorklistProgram.record (ExecCoreChildProgram.formulaCode
--               (DisjointBranchProgram.resultB SubexpFrontend.negateCode F S H)) ++ d.stacks 257) ∧
--           e.stacks 258 = d.stacks 258 ∧ e.stacks 261 = [] ∧ e.stacks 262 = [] ∧
--           e.stacks 265 = [] ∧ e.stacks 259 = d.stacks 259 ∧
--           e.stacks 260 = d.stacks 260
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpFrontend.negateCode` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.clauseCode`, `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.formulaCode`, `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.inputVolume`, `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.result` and `OAI.Algorithms.SubexponentialSAT.ExecWorklistProgram.record` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.resultB` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.Data` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.branch` (definitions bundle `OAIQ081S115` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.body_refinement` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparseDFSProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.branch_execution_from_state)

import Mathlib
import Definitions.Def_OAIQ081S115

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram

open BitProgram StructuredCalls SubexpPostfixControl

theorem branch_execution_from_state (d : Data) (F S : List (List ℕ)) (H : List ℕ)
    (hF : d.stacks 265 = ExecCoreChildProgram.formulaCode F)
    (hH : d.stacks 9 = ExecCoreChildProgram.clauseCode H)
    (hS : d.stacks 12 = ExecCoreChildProgram.formulaCode S)
    (hleft : d.stacks 261 = []) (hright : d.stacks 262 = [])
    (hclean : ∀ i : Fin 1220, i.val < 24 → i ≠ 9 → i ≠ 12 → d.stacks i = []) :
    ∃ t ≤ 621000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2,
      ∃ e, Eval branch t d e ∧
        e.stacks 257 =
          ExecWorklistProgram.record
            (ExecCoreChildProgram.formulaCode (ExecCoreChildProgram.result F S H)) ++
          (ExecWorklistProgram.record (ExecCoreChildProgram.formulaCode
            (DisjointBranchProgram.resultB SubexpFrontend.negateCode F S H)) ++ d.stacks 257) ∧
        e.stacks 258 = d.stacks 258 ∧ e.stacks 261 = [] ∧ e.stacks 262 = [] ∧
        e.stacks 265 = [] ∧ e.stacks 259 = d.stacks 259 ∧
        e.stacks 260 = d.stacks 260 := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram
end
