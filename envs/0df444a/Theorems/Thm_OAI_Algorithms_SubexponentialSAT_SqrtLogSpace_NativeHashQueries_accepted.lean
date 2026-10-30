-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeHashQueries_accepted
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:28:41.608678+00:00
-- url     : https://prove2.me/theorems/bdf8ee0c-565d-41a3-9756-351211b70046
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeHashQueries.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeHashQueries.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries`, with `open BitProgram StructuredCalls SqrtLog DisjointReuse`, `open HighFrontendSources HashGreedyCode HashQueryEntry LeafProgram`, `open HashGreedyProgram.NativeRound`, `open LeafParametersProgram HighMarkedFrontend HighQuerySetup ProducedQueryResources`, `open NativeQueryInputBounds Statement`):
--
--   ```lean
--   theorem accepted (k C0 d0 : ℕ) (hk : 2 ≤ k) :
--       ∃ C E : ℝ, ∃ degree Cs es cutoff : ℕ,
--         1 ≤ C ∧ 1 ≤ E ∧ 1 ≤ degree ∧
--       ∀ n N R : ℕ, cutoff ≤ n → n ≤ N →
--         let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k-1)
--         ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
--         F.length ≤ n*B →
--         ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
--           (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
--         ∀ (base d : State 40 896) (frameBound : ℕ),
--         NativeLeafPreparation.Ready n F.length B (initial shifts Q) base →
--         (∀ i, (base.stacks i).length ≤ R) →
--         base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
--         BinaryArithmetic.toNat (base.stacks 785) = n →
--         NativeLeafRun.commonBound n F.length B R ≤ C0*(N+1)^d0 →
--         (∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
--           base.stacks i = []) →
--         HashGreedyRound.RowBoundary base
--           (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
--             (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) d →
--         let input := AcceptedQueryStage.staged d
--         (∀ i, i ∈ HighQueryProgram.Carried.words → (input.stacks i).length ≤ frameBound) →
--         ∃ steps output,
--           Eval (HighQueryProgram.accepted k) steps input output ∧
--           steps+1 ≤ Nat.ceil (runtimeBound C E degree N n) ∧
--           output.stacks = Function.update input.stacks 788 (countWord
--             (HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
--               (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
--                 (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds))) ∧
--           (output.stacks 788).length ≤ n+1 ∧
--           StageSpace (HighQueryProgram.accepted k) (steps+1) input
--             (max (Cs*(N+1)^es) frameBound)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNF.Clause` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.acceptedCount` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sparsifySchedule` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried.words` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedLocal` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedShifts` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseM` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RawCNF`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.rowAccept`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.commonBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.clauseRecords` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Valid` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.initial` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics.indexed` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage.staged` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.RowBoundary` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.StageSpace` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.Ready` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.accepted` (definitions bundle `OAIQ081S193` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList`, `OAI.Algorithms.SubexponentialSAT.SAT.Assignment`, `OAI.Algorithms.SubexponentialSAT.SAT.Literal`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeBound` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_execution` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeHashQueries.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S193

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries

open BitProgram StructuredCalls SqrtLog DisjointReuse
open HighFrontendSources HashGreedyCode HashQueryEntry LeafProgram
open HashGreedyProgram.NativeRound

open LeafParametersProgram HighMarkedFrontend HighQuerySetup ProducedQueryResources

open NativeQueryInputBounds Statement

attribute [local irreducible] Execute.guardedModel

theorem accepted (k C0 d0 : ℕ) (hk : 2 ≤ k) :
    ∃ C E : ℝ, ∃ degree Cs es cutoff : ℕ,
      1 ≤ C ∧ 1 ≤ E ∧ 1 ≤ degree ∧
    ∀ n N R : ℕ, cutoff ≤ n → n ≤ N →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k-1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
      F.length ≤ n*B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (base d : State 40 896) (frameBound : ℕ),
      NativeLeafPreparation.Ready n F.length B (initial shifts Q) base →
      (∀ i, (base.stacks i).length ≤ R) →
      base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      BinaryArithmetic.toNat (base.stacks 785) = n →
      NativeLeafRun.commonBound n F.length B R ≤ C0*(N+1)^d0 →
      (∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
        base.stacks i = []) →
      HashGreedyRound.RowBoundary base
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) d →
      let input := AcceptedQueryStage.staged d
      (∀ i, i ∈ HighQueryProgram.Carried.words → (input.stacks i).length ≤ frameBound) →
      ∃ steps output,
        Eval (HighQueryProgram.accepted k) steps input output ∧
        steps+1 ≤ Nat.ceil (runtimeBound C E degree N n) ∧
        output.stacks = Function.update input.stacks 788 (countWord
          (HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
            (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
              (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds))) ∧
        (output.stacks 788).length ≤ n+1 ∧
        StageSpace (HighQueryProgram.accepted k) (steps+1) input
          (max (Cs*(N+1)^es) frameBound) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries
end
