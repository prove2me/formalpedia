-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafRun_ready_rounds
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.ready_rounds
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:40:45.592902+00:00
-- url     : https://prove2.me/theorems/39e8b0fb-700b-437c-a826-67cffc997c44
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.ready_rounds: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.ready_rounds` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafRun.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafRun.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun`, with `open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram`, `open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound`, `open HashMassAdapter HashGreedyExecution`):
--
--   ```lean
--   theorem ready_rounds {n m B : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
--       (hm : 0 < m) (initial : List (List Bool)) (depth : ℕ)
--       (hd : depth = SparseCode.distanceDenom m B) (query : Cmd 40 896)
--       (queryCost : List Bool → ℕ) (base : State 40 896)
--       (hr : NativeLeafPreparation.Ready n m B initial base)
--       (L K : ℕ) (hbase : ∀ i, (base.stacks i).length ≤ L)
--       (hB : HashSelect.loopCap n m ≤ L)
--       (hcounterBound : 2 * HashCandidates.payloadWidth m depth + 3 ≤ L)
--       (href : (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 3 * L + 2)
--       (hgrowth : outputGrowth (fun _ => n + 1) (RowSelectionProgram.Index.alphabet m) ≤ 3 * L + 2)
--       (hC : HashCandidates.payloadWidth m depth ≤ L)
--       (hbytesL : (encodedHistory initial).length +
--         HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) ≤ L)
--       (hq : ∀ rows word (d : State 40 896),
--         rows.length ≤ initial.length + HashSelect.loopCap n m →
--         (∃ q ≤ HashSelect.loopCap n m, rows = HashGreedyCNF.history clauses depth initial q) →
--         (encodedHistory rows).length ≤ (encodedHistory initial).length +
--           HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) →
--         word.length = HashCandidates.payloadWidth m depth →
--         (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
--           d.stacks i = base.stacks i) →
--         d.stacks 777 = encodedHistory rows → d.stacks 778 = Encoding.encodeList id [word] →
--         d.stacks 779 = [] → ∀ (e : Fin m) tail (a : State 40 896),
--         Ready (fun words => words = workspace (LeafOuterNative.trialStaged (trialState d m depth word))) a →
--         ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
--           workspace middle = workspace (LeafOuterNative.trialStaged (trialState d m depth word)) ∧
--           read middle = read a ∧
--           BinaryArithmetic.toNat (middle.stacks 323) = markedCount
--             (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth word.reverse :: rows)
--             (fun e x => !(clauses e).eval x) e ∧
--           (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
--           Eval query t
--             (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
--             (state recordPorts middle false true false tail []))
--       (hspace : ∀ rows word (d : State 40 896),
--         rows.length ≤ initial.length + HashSelect.loopCap n m →
--         (∃ q ≤ HashSelect.loopCap n m, rows = HashGreedyCNF.history clauses depth initial q) →
--         (encodedHistory rows).length ≤ (encodedHistory initial).length +
--           HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) →
--         word.length = HashCandidates.payloadWidth m depth →
--         (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
--           d.stacks i = base.stacks i) →
--         d.stacks 777 = encodedHistory rows → d.stacks 778 = Encoding.encodeList id [word] →
--         d.stacks 779 = [] → (∀ i, (d.stacks i).length ≤ L) →
--         ∀ (e : Fin m) tail a t middle,
--         Ready (fun ws => ws = workspace (LeafOuterNative.trialStaged (trialState d m depth word))) a →
--         (read a).length ≤ 3 * L + 2 → tail.length ≤ 3 * L + 2 →
--         (Encoding.encodeNat e.val).length ≤ 3 * L + 2 → n + 1 ≤ 3 * L + 2 →
--         Eval query t (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
--           (state recordPorts middle false true false tail []) →
--         StageSpace query t (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse) K)
--       : ∃ steps out, steps ≤ roundsTime base n m depth queryCost L ∧
--         Eval (roundsCommand query) steps base out ∧
--         RowBoundary base (HashGreedyCNF.history clauses depth
--           initial (HashSelect.loopCap n m)) out ∧
--         out.stacks 781 = [] ∧ out.regs 9 = false ∧
--         (∀ i, (out.stacks i).length ≤ L) ∧
--         StageSpace (roundsCommand query) (steps + 1) base (roundsSpace base n m depth L K)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.outputGrowth` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.RecordPrograms.state` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.Index.alphabet` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.markedCount` (definitions bundle `OAIQ081S039` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.normalize` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.payloadWidth` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.rowAccept` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.recordPorts` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.encodedHistory` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.Data` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution.trialState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.RowBoundary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative.trialStaged` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.StageSpace` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.Ready` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.read` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.workspace` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.roundsCommand` (definitions bundle `OAIQ081S152` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.roundsSpace` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.roundsTime` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat`, `OAI.Algorithms.SubexponentialSAT.SAT.Assignment`, `OAI.Algorithms.SubexponentialSAT.SAT.Clause` and `OAI.Algorithms.SubexponentialSAT.SAT.Clause.eval` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_execution` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafRun.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.ready_rounds)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165

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

theorem ready_rounds {n m B : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (initial : List (List Bool)) (depth : ℕ)
    (hd : depth = SparseCode.distanceDenom m B) (query : Cmd 40 896)
    (queryCost : List Bool → ℕ) (base : State 40 896)
    (hr : NativeLeafPreparation.Ready n m B initial base)
    (L K : ℕ) (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hB : HashSelect.loopCap n m ≤ L)
    (hcounterBound : 2 * HashCandidates.payloadWidth m depth + 3 ≤ L)
    (href : (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 3 * L + 2)
    (hgrowth : outputGrowth (fun _ => n + 1) (RowSelectionProgram.Index.alphabet m) ≤ 3 * L + 2)
    (hC : HashCandidates.payloadWidth m depth ≤ L)
    (hbytesL : (encodedHistory initial).length +
      HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) ≤ L)
    (hq : ∀ rows word (d : State 40 896),
      rows.length ≤ initial.length + HashSelect.loopCap n m →
      (∃ q ≤ HashSelect.loopCap n m, rows = HashGreedyCNF.history clauses depth initial q) →
      (encodedHistory rows).length ≤ (encodedHistory initial).length +
        HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) →
      word.length = HashCandidates.payloadWidth m depth →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
        d.stacks i = base.stacks i) →
      d.stacks 777 = encodedHistory rows → d.stacks 778 = Encoding.encodeList id [word] →
      d.stacks 779 = [] → ∀ (e : Fin m) tail (a : State 40 896),
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged (trialState d m depth word))) a →
      ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
        workspace middle = workspace (LeafOuterNative.trialStaged (trialState d m depth word)) ∧
        read middle = read a ∧
        BinaryArithmetic.toNat (middle.stacks 323) = markedCount
          (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth word.reverse :: rows)
          (fun e x => !(clauses e).eval x) e ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t
          (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
          (state recordPorts middle false true false tail []))
    (hspace : ∀ rows word (d : State 40 896),
      rows.length ≤ initial.length + HashSelect.loopCap n m →
      (∃ q ≤ HashSelect.loopCap n m, rows = HashGreedyCNF.history clauses depth initial q) →
      (encodedHistory rows).length ≤ (encodedHistory initial).length +
        HashSelect.loopCap n m * (2 * HashCandidates.payloadWidth m depth + 2) →
      word.length = HashCandidates.payloadWidth m depth →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
        d.stacks i = base.stacks i) →
      d.stacks 777 = encodedHistory rows → d.stacks 778 = Encoding.encodeList id [word] →
      d.stacks 779 = [] → (∀ i, (d.stacks i).length ≤ L) →
      ∀ (e : Fin m) tail a t middle,
      Ready (fun ws => ws = workspace (LeafOuterNative.trialStaged (trialState d m depth word))) a →
      (read a).length ≤ 3 * L + 2 → tail.length ≤ 3 * L + 2 →
      (Encoding.encodeNat e.val).length ≤ 3 * L + 2 → n + 1 ≤ 3 * L + 2 →
      Eval query t (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query t (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse) K)
    : ∃ steps out, steps ≤ roundsTime base n m depth queryCost L ∧
      Eval (roundsCommand query) steps base out ∧
      RowBoundary base (HashGreedyCNF.history clauses depth
        initial (HashSelect.loopCap n m)) out ∧
      out.stacks 781 = [] ∧ out.regs 9 = false ∧
      (∀ i, (out.stacks i).length ≤ L) ∧
      StageSpace (roundsCommand query) (steps + 1) base (roundsSpace base n m depth L K) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
end
