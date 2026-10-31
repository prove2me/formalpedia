-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafContract_local_from_runs
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_from_runs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:31:04.242668+00:00
-- url     : https://prove2.me/theorems/397ae963-25ce-4277-a778-402cace35c7f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_from_runs: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_from_runs` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract`, with `open BitProgram StructuredCalls DisjointReuse DFSVisit SparseDFSRefinement`, `open SqrtLog HashGreedyProgram.NativeRound HashGreedyRound in`):
--
--   ```lean
--   theorem local_from_runs {n B : ℕ} (k : ℕ) (F : RawCNF n)
--       (hm : 0 < F.length) (hB : 0 < B)
--       (shifts : SparseCode.SuppliedShifts F.length B)
--       (Q : SparseCode.SuppliedLocal F.length B)
--       (hs : WalshExistence.Good (SparseCode.gapDenom F.length B) shifts)
--       (hQ : SparseCode.HasDistance Q
--         (SparseCode.degree F.length B / (100 * B * SparseCode.logSize F.length) + 1))
--       (a base selected middle : State 40 896)
--       (prepareSteps roundSteps querySteps L prepareCap roundCap queryCap : ℕ)
--       (ep : Eval NativeLeafPreparation.command prepareSteps a base)
--       (sp : ∀ t z, t ≤ prepareSteps →
--         Trace (compiled NativeLeafPreparation.command 784 788) t
--           (a.withPC (some (compiled NativeLeafPreparation.command 784 788).entry)) z →
--         ∀ i, (z.stacks i).length ≤ prepareCap)
--       (hr : NativeLeafPreparation.Ready n F.length B (HashGreedyCode.initial shifts Q) base)
--       (hselected : RowBoundary base
--         (HashGreedyCNF.history (NativeLeafSemantics.indexed F) (SparseCode.distanceDenom F.length B)
--           (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)) selected)
--       (ha : ∀ i, (selected.stacks i).length ≤ L) (hn : n + 1 ≤ L)
--       (er : Eval (NativeLeafRun.roundsCommand (HighQueryProgram.marked k)) roundSteps base selected)
--       (sr : StageSpace (NativeLeafRun.roundsCommand (HighQueryProgram.marked k))
--         (roundSteps + 1) base roundCap)
--       (eq : Eval (HighQueryProgram.accepted k) querySteps (AcceptedQueryStage.staged selected) middle)
--       (hword : middle.stacks = Function.update (AcceptedQueryStage.staged selected).stacks 788
--         (countWord (HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
--           (HashGreedyCNF.history (NativeLeafSemantics.indexed F) (SparseCode.distanceDenom F.length B)
--             (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)))))
--       (sq : StageSpace (HighQueryProgram.accepted k) querySteps
--         (AcceptedQueryStage.staged selected) queryCap) :
--       ∃ steps out,
--         steps + 1 ≤ prepareSteps + roundSteps + querySteps + 61 * L + 71 ∧
--         Eval (NativeLeafProgram.localCommand k) steps a out ∧
--         out.stacks = Function.update selected.stacks 788 (countWord (rawCount F)) ∧
--         out.stacks 788 = countWord (rawCount F) ∧
--         (∀ i, (out.stacks i).length ≤ L) ∧
--         ∀ t z, t ≤ steps + 1 → Trace (NativeLeafProgram.localProgram k) t
--           (a.withPC (some (NativeLeafProgram.localProgram k).entry)) z →
--           ∀ i, (z.stacks i).length ≤
--             max prepareCap (max roundCap (max queryCap (1000 * L + 100)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNF.Clause` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.degree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.dimension`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.gapDenom`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.localRows` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.logSize` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.acceptedCount` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedShifts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.Good` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.HasDistance` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RawCNF`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.rawCount` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.rowAccept` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.initial` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics.indexed` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage.staged` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.RowBoundary` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.StageSpace` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.Ready` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.roundsCommand` (definitions bundle `OAIQ081S152` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.command` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafProgram.localCommand` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafProgram.localProgram` (definitions bundle `OAIQ081S193` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Assignment`, `OAI.Algorithms.SubexponentialSAT.SAT.Literal` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_execution` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_from_runs)

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

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
open BitProgram StructuredCalls DisjointReuse DFSVisit SparseDFSRefinement

open SqrtLog HashGreedyProgram.NativeRound HashGreedyRound in
theorem local_from_runs {n B : ℕ} (k : ℕ) (F : RawCNF n)
    (hm : 0 < F.length) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B)
    (hs : WalshExistence.Good (SparseCode.gapDenom F.length B) shifts)
    (hQ : SparseCode.HasDistance Q
      (SparseCode.degree F.length B / (100 * B * SparseCode.logSize F.length) + 1))
    (a base selected middle : State 40 896)
    (prepareSteps roundSteps querySteps L prepareCap roundCap queryCap : ℕ)
    (ep : Eval NativeLeafPreparation.command prepareSteps a base)
    (sp : ∀ t z, t ≤ prepareSteps →
      Trace (compiled NativeLeafPreparation.command 784 788) t
        (a.withPC (some (compiled NativeLeafPreparation.command 784 788).entry)) z →
      ∀ i, (z.stacks i).length ≤ prepareCap)
    (hr : NativeLeafPreparation.Ready n F.length B (HashGreedyCode.initial shifts Q) base)
    (hselected : RowBoundary base
      (HashGreedyCNF.history (NativeLeafSemantics.indexed F) (SparseCode.distanceDenom F.length B)
        (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)) selected)
    (ha : ∀ i, (selected.stacks i).length ≤ L) (hn : n + 1 ≤ L)
    (er : Eval (NativeLeafRun.roundsCommand (HighQueryProgram.marked k)) roundSteps base selected)
    (sr : StageSpace (NativeLeafRun.roundsCommand (HighQueryProgram.marked k))
      (roundSteps + 1) base roundCap)
    (eq : Eval (HighQueryProgram.accepted k) querySteps (AcceptedQueryStage.staged selected) middle)
    (hword : middle.stacks = Function.update (AcceptedQueryStage.staged selected).stacks 788
      (countWord (HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F) (SparseCode.distanceDenom F.length B)
          (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)))))
    (sq : StageSpace (HighQueryProgram.accepted k) querySteps
      (AcceptedQueryStage.staged selected) queryCap) :
    ∃ steps out,
      steps + 1 ≤ prepareSteps + roundSteps + querySteps + 61 * L + 71 ∧
      Eval (NativeLeafProgram.localCommand k) steps a out ∧
      out.stacks = Function.update selected.stacks 788 (countWord (rawCount F)) ∧
      out.stacks 788 = countWord (rawCount F) ∧
      (∀ i, (out.stacks i).length ≤ L) ∧
      ∀ t z, t ≤ steps + 1 → Trace (NativeLeafProgram.localProgram k) t
        (a.withPC (some (NativeLeafProgram.localProgram k).entry)) z →
        ∀ i, (z.stacks i).length ≤
          max prepareCap (max roundCap (max queryCap (1000 * L + 100))) := by
  sorry

open SqrtLog Filter
open scoped Topology

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
end
