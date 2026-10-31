-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashQueryEntry_prepared_trial_entry
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.prepared_trial_entry
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:56:09.195484+00:00
-- url     : https://prove2.me/theorems/19ea9020-e397-4cdd-9b46-1cb06f89a7af
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.prepared_trial_entry: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.prepared_trial_entry` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashQueryEntry.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashQueryEntry.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry`, with `open BitProgram StructuredCalls SqrtLog`, `open HighFrontendSources HashGreedyCode`):
--
--   ```lean
--   theorem prepared_trial_entry {n B : ℕ} (F : DisjointReuse.RawCNF n) (hn : 0 < n)
--       (hm : 0 < F.length) (shifts : SparseCode.SuppliedShifts F.length B)
--       (Q : SparseCode.SuppliedLocal F.length B) (rounds : ℕ) (word : List Bool)
--       (base d a : Data) (e : Fin F.length) (tail : List Bool)
--       (hbase : NativeLeafPreparation.Ready n F.length B (initial shifts Q) base)
--       (hformula : base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F))
--       (hambient : BinaryArithmetic.toNat (base.stacks 785) = n)
--       (hword : word.length = HashCandidates.payloadWidth F.length
--         (SparseCode.distanceDenom F.length B))
--       (hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
--         d.stacks i = base.stacks i)
--       (hhistory : d.stacks 777 = HashGreedyProgram.encodedHistory
--         (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
--           (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds))
--       (hready : HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace
--         (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d F.length
--           (SparseCode.distanceDenom F.length B) word))) a) :
--       MarkedEntry (trialQuery F hm shifts Q rounds word e d)
--         (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d F.length
--           (SparseCode.distanceDenom F.length B) word))
--         (recordState a tail (Encoding.encodeNat e.val))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNF.Clause` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedLocal` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedShifts` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.payloadWidth` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RawCNF` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.clauseRecords` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.initial` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics.indexed` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.encodedHistory` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution.trialState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.recordState` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative.trialStaged` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.Ready` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.Ready` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.workspace` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.MarkedEntry` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.trialQuery` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.marked_with_shadow` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashQueryEntry.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.prepared_trial_entry)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S172

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry

open BitProgram StructuredCalls SqrtLog
open HighFrontendSources HashGreedyCode

theorem prepared_trial_entry {n B : ℕ} (F : DisjointReuse.RawCNF n) (hn : 0 < n)
    (hm : 0 < F.length) (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B) (rounds : ℕ) (word : List Bool)
    (base d a : Data) (e : Fin F.length) (tail : List Bool)
    (hbase : NativeLeafPreparation.Ready n F.length B (initial shifts Q) base)
    (hformula : base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F))
    (hambient : BinaryArithmetic.toNat (base.stacks 785) = n)
    (hword : word.length = HashCandidates.payloadWidth F.length
      (SparseCode.distanceDenom F.length B))
    (hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i)
    (hhistory : d.stacks 777 = HashGreedyProgram.encodedHistory
      (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
        (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds))
    (hready : HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace
      (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d F.length
        (SparseCode.distanceDenom F.length B) word))) a) :
    MarkedEntry (trialQuery F hm shifts Q rounds word e d)
      (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d F.length
        (SparseCode.distanceDenom F.length B) word))
      (recordState a tail (Encoding.encodeNat e.val)) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry
end
