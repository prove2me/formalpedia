-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeHashQuerySetup_accepted_with_shadow
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.accepted_with_shadow
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:09:55.335102+00:00
-- url     : https://prove2.me/theorems/92b396ab-7fc0-407a-90a7-ae2780c72d06
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.accepted_with_shadow: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.accepted_with_shadow` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeHashQuerySetup.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeHashQuerySetup.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup`, with `open BitProgram StructuredCalls SqrtLog DisjointReuse LeafParametersProgram`, `open HashGreedyCode HashQueryEntry HighFrontendSources NativeQueryInputBounds`, `open HighMarkedFrontend HighQuerySetup ProducedQueryResources`, `open HashGreedyProgram.NativeRound`):
--
--   ```lean
--   theorem accepted_with_shadow (k : ℕ) (hk : 2 ≤ k) :
--       ∃ Cp dp Cn dn Cl dl Cf df cutoff : ℕ,
--       ∀ n N R : ℕ, cutoff ≤ n → n ≤ N →
--         let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k-1)
--         ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
--         F.length ≤ n*B →
--         ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
--           (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
--         ∀ (base d : Data) (hidden : ℕ),
--         NativeLeafPreparation.Ready n F.length B (initial shifts Q) base →
--         (∀ i, (base.stacks i).length ≤ R) →
--         base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
--         BinaryArithmetic.toNat (base.stacks 785) = n →
--         HashGreedyRound.RowBoundary base
--           (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
--             (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) d →
--         let input := AcceptedQueryStage.staged d
--         (∀ i, H i → (input.stacks i).length ≤ hidden) →
--         let q := acceptedQuery F hm shifts Q rounds d
--         let L := NativeLeafRun.commonBound n F.length B R
--         let S := sourceCap Cn dn Cl dl N L k
--         let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
--         AcceptedEntry q input ∧ ambient q = n ∧
--         q.index = Encoding.encodeNat (LeafProgram.PreparedSource.markIndex q) ∧
--         1 ≤ S ∧ n^2 ≤ S ∧ (q.input k).incidences ≤ S ∧
--         (∀ padding j, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).val j ≤ S ∧
--           (Execute.guardedModel (q.input k) padding).val j ≤ S) ∧
--         HighMarkedFrontend.acceptedBudget q k ≤ frontendCap Cf df L k ∧
--         Nonempty (SetupRun q k input (HighMarkedFrontend.acceptedCommand k)
--           (LeafProgram.Query.unmarkedInput (project input)) (HighMarkedFrontend.acceptedBudget q k)
--           S hidden Cp dp (frontendCap Cf df L k + 111*P+81) (12*P+4*N+6)) ∧
--         Nonempty (SetupRun q k (HighQueryEntryShadow.erase input) (HighMarkedFrontend.acceptedCommand k)
--           (LeafProgram.Query.unmarkedInput (project (HighQueryEntryShadow.erase input)))
--           (HighMarkedFrontend.acceptedBudget q k) S 0 Cp dp
--           (frontendCap Cf df L k + 111*P+81) (12*P+4*N+6))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNF.Clause` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Input` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sparsifySchedule`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds.frontendCap`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds.preparedCap`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds.sourceCap` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried.words` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedLocal` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedShifts` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseM` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RawCNF`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.commonBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.clauseRecords` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Valid` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.result` (definitions bundle `OAIQ081S067` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.unmarkedInput` (definitions bundle `OAIQ081S077` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.initial` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics.indexed` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.project` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage.staged` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.RowBoundary` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.Ready` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.guardedModel` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.code` (definitions bundle `OAIQ081S153` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ambient` (definitions bundle `OAIQ081S171` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.AcceptedEntry` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.acceptedQuery` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.markIndex` (definitions bundle `OAIQ081S175` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow.erase` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.Data` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.acceptedCommand` (definitions bundle `OAIQ081S183` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.acceptedBudget` (definitions bundle `OAIQ081S186` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.SetupRun` (definitions bundle `OAIQ081S190` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeHashQuerySetup.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.accepted_with_shadow)

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

theorem accepted_with_shadow (k : ℕ) (hk : 2 ≤ k) :
    ∃ Cp dp Cn dn Cl dl Cf df cutoff : ℕ,
    ∀ n N R : ℕ, cutoff ≤ n → n ≤ N →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k-1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
      F.length ≤ n*B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (base d : Data) (hidden : ℕ),
      NativeLeafPreparation.Ready n F.length B (initial shifts Q) base →
      (∀ i, (base.stacks i).length ≤ R) →
      base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      BinaryArithmetic.toNat (base.stacks 785) = n →
      HashGreedyRound.RowBoundary base
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) d →
      let input := AcceptedQueryStage.staged d
      (∀ i, H i → (input.stacks i).length ≤ hidden) →
      let q := acceptedQuery F hm shifts Q rounds d
      let L := NativeLeafRun.commonBound n F.length B R
      let S := sourceCap Cn dn Cl dl N L k
      let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
      AcceptedEntry q input ∧ ambient q = n ∧
      q.index = Encoding.encodeNat (LeafProgram.PreparedSource.markIndex q) ∧
      1 ≤ S ∧ n^2 ≤ S ∧ (q.input k).incidences ≤ S ∧
      (∀ padding j, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).val j ≤ S ∧
        (Execute.guardedModel (q.input k) padding).val j ≤ S) ∧
      HighMarkedFrontend.acceptedBudget q k ≤ frontendCap Cf df L k ∧
      Nonempty (SetupRun q k input (HighMarkedFrontend.acceptedCommand k)
        (LeafProgram.Query.unmarkedInput (project input)) (HighMarkedFrontend.acceptedBudget q k)
        S hidden Cp dp (frontendCap Cf df L k + 111*P+81) (12*P+4*N+6)) ∧
      Nonempty (SetupRun q k (HighQueryEntryShadow.erase input) (HighMarkedFrontend.acceptedCommand k)
        (LeafProgram.Query.unmarkedInput (project (HighQueryEntryShadow.erase input)))
        (HighMarkedFrontend.acceptedBudget q k) S 0 Cp dp
        (frontendCap Cf df L k + 111*P+81) (12*P+4*N+6)) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup
end
