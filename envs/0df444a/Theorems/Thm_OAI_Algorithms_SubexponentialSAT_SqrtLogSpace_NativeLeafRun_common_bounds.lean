-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafRun_common_bounds
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.common_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:20:50.992819+00:00
-- url     : https://prove2.me/theorems/187404b1-6e74-4022-99f3-8b4f2baa1d5a
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.common_bounds: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.common_bounds` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafRun.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafRun.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun`, with `open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram`, `open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound`, `open HashMassAdapter HashGreedyExecution`):
--
--   ```lean
--   theorem common_bounds {n m B : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
--       (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
--       (wordBound : ℕ) :
--       let L := commonBound n m B wordBound
--       wordBound ≤ L ∧ HashSelect.loopCap n m ≤ L ∧
--         HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) ≤ L ∧
--         2 * HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) + 3 ≤ L ∧
--         (encodedHistory (HashGreedyCode.initial shifts Q)).length + HashSelect.loopCap n m *
--           (2 * HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) + 2) ≤ L ∧
--         (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 3 * L + 2 ∧
--         outputGrowth (fun _ => n + 1) (RowSelectionProgram.Index.alphabet m) ≤ 3 * L + 2 ∧
--         n + 1 ≤ L
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.outputGrowth` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.Index.alphabet` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedLocal` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedShifts` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.payloadWidth` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.commonBound` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.initial` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.encodedHistory` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.SAT.Clause` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.accepted_with_shadow`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.marked_with_shadow` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_execution` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafRun.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.common_bounds)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound
open HashMassAdapter HashGreedyExecution

theorem common_bounds {n m B : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (wordBound : ℕ) :
    let L := commonBound n m B wordBound
    wordBound ≤ L ∧ HashSelect.loopCap n m ≤ L ∧
      HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) ≤ L ∧
      2 * HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) + 3 ≤ L ∧
      (encodedHistory (HashGreedyCode.initial shifts Q)).length + HashSelect.loopCap n m *
        (2 * HashCandidates.payloadWidth m (SparseCode.distanceDenom m B) + 2) ≤ L ∧
      (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 3 * L + 2 ∧
      outputGrowth (fun _ => n + 1) (RowSelectionProgram.Index.alphabet m) ≤ 3 * L + 2 ∧
      n + 1 ≤ L := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
end
