-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeHashQuerySetup_marked_with_shadow
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.marked_with_shadow
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:09:24.093389+00:00
-- url     : https://prove2.me/theorems/ba485096-f9d5-4071-91e2-3e5907e78728
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.marked_with_shadow: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.marked_with_shadow` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeHashQuerySetup.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeHashQuerySetup.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup`, with `open BitProgram StructuredCalls SqrtLog DisjointReuse LeafParametersProgram`, `open HashGreedyCode HashQueryEntry HighFrontendSources NativeQueryInputBounds`, `open HighMarkedFrontend HighQuerySetup ProducedQueryResources`, `open HashGreedyProgram.NativeRound`):
--
--   ```lean
--   theorem marked_with_shadow (k : ℕ) (hk : 2 ≤ k) :
--       ∃ Cp dp Cn dn Cl dl Cf df cutoff : ℕ,
--       ∀ n N R : ℕ, cutoff ≤ n → n ≤ N →
--         let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k-1)
--         ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
--         F.length ≤ n*B →
--         ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
--           (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
--         ∀ (word : List Bool) (base d a : Data) (e : Fin F.length) (tail : List Bool) (hidden : ℕ),
--         NativeLeafPreparation.Ready n F.length B (initial shifts Q) base →
--         (∀ i, (base.stacks i).length ≤ R) →
--         base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
--         BinaryArithmetic.toNat (base.stacks 785) = n →
--         word.length = HashCandidates.payloadWidth F.length (SparseCode.distanceDenom F.length B) →
--         (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
--           d.stacks i = base.stacks i) →
--         d.stacks 777 = HashGreedyProgram.encodedHistory
--           (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
--             (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) →
--         d.stacks 778 = Encoding.encodeList id [word] → d.stacks 779 = [] →
--         HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace
--           (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d F.length
--             (SparseCode.distanceDenom F.length B) word))) a →
--         let input := recordState a tail (Encoding.encodeNat e.val)
--         (∀ i, H i → (input.stacks i).length ≤ hidden) →
--         let q := trialQuery F hm shifts Q rounds word e d
--         let L := NativeLeafRun.commonBound n F.length B R
--         let S := sourceCap Cn dn Cl dl N L k
--         let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
--         MarkedEntry q (LeafOuterNative.trialStaged
--           (HashGreedyExecution.trialState d F.length (SparseCode.distanceDenom F.length B) word)) input ∧
--         ambient q = n ∧ q.index = Encoding.encodeNat (LeafProgram.PreparedSource.markIndex q) ∧
--         1 ≤ S ∧ n^2 ≤ S ∧ (q.input k).incidences ≤ S ∧
--         (∀ padding j, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).val j ≤ S ∧
--           (Execute.guardedModel (q.input k) padding).val j ≤ S) ∧
--         HighMarkedFrontend.budget q k ≤ frontendCap Cf df L k ∧
--         Nonempty (SetupRun q k input (HighMarkedFrontend.command k)
--           (LeafProgram.Query.markedInput (project input)) (HighMarkedFrontend.budget q k)
--           S hidden Cp dp (frontendCap Cf df L k + 111*P+81) (12*P+4*N+6)) ∧
--         Nonempty (SetupRun q k (HighQueryEntryShadow.erase input) (HighMarkedFrontend.command k)
--           (LeafProgram.Query.markedInput (project (HighQueryEntryShadow.erase input)))
--           (HighMarkedFrontend.budget q k) S 0 Cp dp
--           (frontendCap Cf df L k + 111*P+81) (12*P+4*N+6))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNF.Clause` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Input` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sparsifySchedule`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds.frontendCap`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds.preparedCap`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds.sourceCap` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried.words` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedLocal` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedShifts` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.payloadWidth` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseM` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RawCNF`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.commonBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.clauseRecords` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Valid` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.result` (definitions bundle `OAIQ081S067` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.markedInput` (definitions bundle `OAIQ081S077` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.initial` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics.indexed` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.project` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.encodedHistory` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution.trialState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.recordState` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative.trialStaged` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.Ready` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.Ready` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.workspace` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.guardedModel` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.code` (definitions bundle `OAIQ081S153` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ambient` (definitions bundle `OAIQ081S171` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.MarkedEntry` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.trialQuery` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.markIndex` (definitions bundle `OAIQ081S175` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow.erase` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.Data` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command` (definitions bundle `OAIQ081S183` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.budget` (definitions bundle `OAIQ081S186` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.SetupRun` (definitions bundle `OAIQ081S190` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeHashQuerySetup.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.marked_with_shadow)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup

open BitProgram StructuredCalls SqrtLog DisjointReuse LeafParametersProgram
open HashGreedyCode HashQueryEntry HighFrontendSources NativeQueryInputBounds
open HighMarkedFrontend HighQuerySetup ProducedQueryResources
open HashGreedyProgram.NativeRound

local notation "H" => (fun i : Fin 896 => i ∈ HighQueryProgram.Carried.words)

theorem marked_with_shadow (k : ℕ) (hk : 2 ≤ k) :
    ∃ Cp dp Cn dn Cl dl Cf df cutoff : ℕ,
    ∀ n N R : ℕ, cutoff ≤ n → n ≤ N →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k-1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
      F.length ≤ n*B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (word : List Bool) (base d a : Data) (e : Fin F.length) (tail : List Bool) (hidden : ℕ),
      NativeLeafPreparation.Ready n F.length B (initial shifts Q) base →
      (∀ i, (base.stacks i).length ≤ R) →
      base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      BinaryArithmetic.toNat (base.stacks 785) = n →
      word.length = HashCandidates.payloadWidth F.length (SparseCode.distanceDenom F.length B) →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
        d.stacks i = base.stacks i) →
      d.stacks 777 = HashGreedyProgram.encodedHistory
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) →
      d.stacks 778 = Encoding.encodeList id [word] → d.stacks 779 = [] →
      HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace
        (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d F.length
          (SparseCode.distanceDenom F.length B) word))) a →
      let input := recordState a tail (Encoding.encodeNat e.val)
      (∀ i, H i → (input.stacks i).length ≤ hidden) →
      let q := trialQuery F hm shifts Q rounds word e d
      let L := NativeLeafRun.commonBound n F.length B R
      let S := sourceCap Cn dn Cl dl N L k
      let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
      MarkedEntry q (LeafOuterNative.trialStaged
        (HashGreedyExecution.trialState d F.length (SparseCode.distanceDenom F.length B) word)) input ∧
      ambient q = n ∧ q.index = Encoding.encodeNat (LeafProgram.PreparedSource.markIndex q) ∧
      1 ≤ S ∧ n^2 ≤ S ∧ (q.input k).incidences ≤ S ∧
      (∀ padding j, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).val j ≤ S ∧
        (Execute.guardedModel (q.input k) padding).val j ≤ S) ∧
      HighMarkedFrontend.budget q k ≤ frontendCap Cf df L k ∧
      Nonempty (SetupRun q k input (HighMarkedFrontend.command k)
        (LeafProgram.Query.markedInput (project input)) (HighMarkedFrontend.budget q k)
        S hidden Cp dp (frontendCap Cf df L k + 111*P+81) (12*P+4*N+6)) ∧
      Nonempty (SetupRun q k (HighQueryEntryShadow.erase input) (HighMarkedFrontend.command k)
        (LeafProgram.Query.markedInput (project (HighQueryEntryShadow.erase input)))
        (HighMarkedFrontend.budget q k) S 0 Cp dp
        (frontendCap Cf df L k + 111*P+81) (12*P+4*N+6)) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup
end
