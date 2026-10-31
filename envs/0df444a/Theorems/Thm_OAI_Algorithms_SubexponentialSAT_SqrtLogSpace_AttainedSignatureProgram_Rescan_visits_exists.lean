-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram_Rescan_visits_exists
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.visits_exists
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:42:27.433017+00:00
-- url     : https://prove2.me/theorems/d69846aa-e333-49eb-815a-91bc05e19e69
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.visits_exists: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.visits_exists` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/AttainedSignatureRescan.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/AttainedSignatureRescan.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan`, with `open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram`):
--
--   ```lean
--   theorem visits_exists (W : List Bool) (rows : List (List (List Bool))) (h B : ℕ)
--       (hlen : ∀ row ∈ rows, row.length = h)
--       (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
--       (candidate : Fin (2 ^ h)) (remaining : ℕ)
--       (i : ℕ) (fuel : List Bool) (regs : Fin 16 → Bool)
--       (htotal : i + remaining = candidate.val) (hl : fuel.length = h)
--       (hv : CounterPrograms.value fuel = remaining)
--       (hf : regs 15 = !(CounterPrograms.isZero fuel)) :
--       ∃ costs n out,
--         CounterForPrograms.Visits countdownPorts body costs n
--           (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
--             (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h i) fuel
--             (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate i)) [] [])
--           (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
--             (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h candidate)
--             (List.replicate h false)
--             (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []) ∧
--         costs.sum ≤ remaining * bodyBound W (naturalKey W rows h candidate) rows h B
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.CounterPrograms.isZero` and `OAI.Algorithms.SubexponentialSAT.CounterPrograms.value` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.fixedBits` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.duplicateScan` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.bodyBound` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.Visits` (definitions bundle `OAIQ081S066` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.countdownPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.naturalKey` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.workState` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.body` (definitions bundle `OAIQ081S136` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.candidate_stack_bound` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.command_eval` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/AttainedSignatureRescan.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.visits_exists)

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

theorem visits_exists (W : List Bool) (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (remaining : ℕ)
    (i : ℕ) (fuel : List Bool) (regs : Fin 16 → Bool)
    (htotal : i + remaining = candidate.val) (hl : fuel.length = h)
    (hv : CounterPrograms.value fuel = remaining)
    (hf : regs 15 = !(CounterPrograms.isZero fuel)) :
    ∃ costs n out,
      CounterForPrograms.Visits countdownPorts body costs n
        (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h i) fuel
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate i)) [] [])
        (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h candidate)
          (List.replicate h false)
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []) ∧
      costs.sum ≤ remaining * bodyBound W (naturalKey W rows h candidate) rows h B := by
  sorry

end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end
