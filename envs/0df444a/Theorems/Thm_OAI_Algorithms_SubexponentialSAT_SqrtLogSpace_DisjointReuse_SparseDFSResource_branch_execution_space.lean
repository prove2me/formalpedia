-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSResource_branch_execution_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource.branch_execution_space
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:15:43.19785+00:00
-- url     : https://prove2.me/theorems/421664a5-6d1e-43bb-93b7-472cc24bae9a
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource.branch_execution_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource.branch_execution_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparseDFSResource.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparseDFSResource.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource`, with `open BitProgram StructuredCalls SparseDFSProgram`):
--
--   ```lean
--   theorem branch_execution_space (frame : Data) (regs : Fin 15 → Bool)
--       (pending header : List Bool) (F S : List (List ℕ)) (H : List ℕ)
--       (frameBound : ℕ) (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
--       ∃ t ≤ 621000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2, ∃ e,
--         Eval branch t (embedState (registers 15 (by decide)) splitterStack frame
--           (DisjointBranchProgram.inputState regs pending header F S H)) e ∧
--         ∀ prefixSteps c, prefixSteps ≤ t →
--           Trace (compiled branch 256 256) prefixSteps
--             ((embedState (registers 15 (by decide)) splitterStack frame
--               (DisjointBranchProgram.inputState regs pending header F S H)).withPC
--                 (some (compiled branch 256 256).entry)) c →
--           ∀ i, (c.stacks i).length ≤ max frameBound
--             (pending.length + header.length + 620001 * (ExecCoreChildProgram.inputVolume F S H) ^ 2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.registers` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.splitterStack` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` and `OAI.Algorithms.SubexponentialSAT.StructuredCalls.embedState` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.inputVolume` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.inputState` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.Data` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.branch` (definitions bundle `OAIQ081S115` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.body_refinement` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparseDFSResource.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource.branch_execution_space)

import Mathlib
import Definitions.Def_OAIQ081S115

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource

open BitProgram StructuredCalls SparseDFSProgram

theorem branch_execution_space (frame : Data) (regs : Fin 15 → Bool)
    (pending header : List Bool) (F S : List (List ℕ)) (H : List ℕ)
    (frameBound : ℕ) (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∃ t ≤ 621000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2, ∃ e,
      Eval branch t (embedState (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.inputState regs pending header F S H)) e ∧
      ∀ prefixSteps c, prefixSteps ≤ t →
        Trace (compiled branch 256 256) prefixSteps
          ((embedState (registers 15 (by decide)) splitterStack frame
            (DisjointBranchProgram.inputState regs pending header F S H)).withPC
              (some (compiled branch 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ max frameBound
          (pending.length + header.length + 620001 * (ExecCoreChildProgram.inputVolume F S H) ^ 2) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource
end
