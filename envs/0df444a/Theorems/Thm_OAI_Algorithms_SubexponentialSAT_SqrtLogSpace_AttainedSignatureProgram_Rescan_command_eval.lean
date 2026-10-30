-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram_Rescan_command_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.command_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:42:42.826559+00:00
-- url     : https://prove2.me/theorems/1cb11b01-eb75-4567-9972-d8ba23d66fbc
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.command_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.command_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/AttainedSignatureRescan.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/AttainedSignatureRescan.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan`, with `open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram`):
--
--   ```lean
--   theorem command_eval (regs : Fin 16 → Bool) (W : List Bool)
--       (rows : List (List (List Bool))) (h B : ℕ)
--       (hlen : ∀ row ∈ rows, row.length = h)
--       (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
--       (candidate : Fin (2 ^ h)) (fresh : Bool) :
--       ∃ n ≤ candidate.val *
--           (bodyBound W (naturalKey W rows h candidate) rows h B + 16 * h + 16) + 20 * h + 26,
--         ∃ out, Eval command n
--           (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
--             (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
--             [] fresh [] [])
--           (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
--             (naturalKey W rows h candidate) (List.replicate h false) []
--             (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] [])
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.fixedBits` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.duplicateScan` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.bodyBound` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.naturalKey` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.workState` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.command` (definitions bundle `OAIQ081S136` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.candidate_stack_bound` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge.probe_run_space` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/AttainedSignatureRescan.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.command_eval)

import Mathlib
import Definitions.Def_OAIQ081S136

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

namespace Rescan

theorem command_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (fresh : Bool) :
    ∃ n ≤ candidate.val *
        (bodyBound W (naturalKey W rows h candidate) rows h B + 16 * h + 16) + 20 * h + 26,
      ∃ out, Eval command n
        (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
          [] fresh [] [])
        (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (List.replicate h false) []
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []) := by
  sorry

end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end
