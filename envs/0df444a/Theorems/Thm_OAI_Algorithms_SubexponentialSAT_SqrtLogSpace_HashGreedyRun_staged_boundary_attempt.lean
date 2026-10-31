-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyRun_staged_boundary_attempt
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun.staged_boundary_attempt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:12:14.764744+00:00
-- url     : https://prove2.me/theorems/4e5e9ff8-05b2-45a4-b293-4a690bdecade
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun.staged_boundary_attempt: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun.staged_boundary_attempt` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyRun.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyRun.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun`, with `open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram`, `open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound`, `open HashMassAdapter HashGreedyExecution`):
--
--   ```lean
--   theorem staged_boundary_attempt {n m depth : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
--       (hm : 0 < m) (query : Cmd 40 896) (queryCost : List Bool → ℕ)
--       (base : State 40 896)
--       (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
--       (hlow : ∀ i : Fin 896, i.val < 12 → base.stacks i = [])
--       (ht : base.stacks 767 = [])
--       (hwidth : (base.stacks 780).length = HashCandidates.digitWidth m)
--       (hvalue : BinaryArithmetic.toNat (base.stacks 780) = 3 * m)
--       (hmword : CounterPrograms.value (base.stacks 782) = m)
--       (hshape : (base.stacks 818).length = HashSelect.loopCap n m)
--       (hcollector : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → base.stacks i = [])
--       (L : ℕ)
--       (hsource : ∀ i ∈ ([782,783,784,785] : List (Fin 896)), (base.stacks i).length ≤ L)
--       (hC : HashCandidates.payloadWidth m depth ≤ L)
--       (hempty : ∀ i ∈ HashMassStaged.stagedPorts, base.stacks i = [])
--       (rows : List (List Bool)) (a : State 40 896) (ha : RowBoundary base rows a)
--       (hbytes : (encodedHistory rows).length ≤ L)
--       (words : List (List Bool)) (d : State 40 896)
--       (hwords : words.map List.length = [HashCandidates.payloadWidth m depth])
--       (hd : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i)
--       (hcounterD : d.stacks 778 = Encoding.encodeList id words) (hsD : d.stacks 779 = [])
--       (hq : ∀ (e : Fin m) tail (a : State 40 896),
--         Ready (fun ws => ws = workspace
--           (LeafOuterNative.trialStaged (trialState d m depth words.flatten))) a →
--         ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
--           workspace middle = workspace (LeafOuterNative.trialStaged (trialState d m depth words.flatten)) ∧
--           read middle = read a ∧
--           BinaryArithmetic.toNat (middle.stacks 323) = markedCount
--             (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth words.flatten.reverse :: rows)
--             (fun e x => !(clauses e).eval x) e ∧
--           (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
--           Eval query t
--             (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
--             (state recordPorts middle false true false tail [])) :
--       ∃ t ≤ stagedAttemptBudget base n m depth queryCost L, ∃ b,
--         Eval (attempt (HashMassStaged.command query)) t d b ∧
--         b.stacks = Function.update (Function.update d.stacks 768
--           (HashGreedyCNF.entry clauses depth rows (CounterPrograms.value words.flatten)).payload) 769
--           (HashGreedyCNF.entry clauses depth rows (CounterPrograms.value words.flatten)).score
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.CounterPrograms.value` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgmin.Entry` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged.stagedPorts` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.RecordPrograms.state` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.markedCount` (definitions bundle `OAIQ081S039` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.digitWidth`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.normalize` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.payloadWidth` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.rowAccept` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.recordPorts` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.encodedHistory` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.attempt` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.Data` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution.trialState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.RowBoundary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative.trialStaged` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.CoreClean` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution.stagedAttemptBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.read` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.workspace` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat`, `OAI.Algorithms.SubexponentialSAT.SAT.Assignment`, `OAI.Algorithms.SubexponentialSAT.SAT.Clause` and `OAI.Algorithms.SubexponentialSAT.SAT.Clause.eval` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.ready_rounds` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyRun.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun.staged_boundary_attempt)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound
open HashMassAdapter HashGreedyExecution

theorem staged_boundary_attempt {n m depth : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (query : Cmd 40 896) (queryCost : List Bool → ℕ)
    (base : State 40 896)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hlow : ∀ i : Fin 896, i.val < 12 → base.stacks i = [])
    (ht : base.stacks 767 = [])
    (hwidth : (base.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (base.stacks 780) = 3 * m)
    (hmword : CounterPrograms.value (base.stacks 782) = m)
    (hshape : (base.stacks 818).length = HashSelect.loopCap n m)
    (hcollector : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → base.stacks i = [])
    (L : ℕ)
    (hsource : ∀ i ∈ ([782,783,784,785] : List (Fin 896)), (base.stacks i).length ≤ L)
    (hC : HashCandidates.payloadWidth m depth ≤ L)
    (hempty : ∀ i ∈ HashMassStaged.stagedPorts, base.stacks i = [])
    (rows : List (List Bool)) (a : State 40 896) (ha : RowBoundary base rows a)
    (hbytes : (encodedHistory rows).length ≤ L)
    (words : List (List Bool)) (d : State 40 896)
    (hwords : words.map List.length = [HashCandidates.payloadWidth m depth])
    (hd : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i)
    (hcounterD : d.stacks 778 = Encoding.encodeList id words) (hsD : d.stacks 779 = [])
    (hq : ∀ (e : Fin m) tail (a : State 40 896),
      Ready (fun ws => ws = workspace
        (LeafOuterNative.trialStaged (trialState d m depth words.flatten))) a →
      ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
        workspace middle = workspace (LeafOuterNative.trialStaged (trialState d m depth words.flatten)) ∧
        read middle = read a ∧
        BinaryArithmetic.toNat (middle.stacks 323) = markedCount
          (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth words.flatten.reverse :: rows)
          (fun e x => !(clauses e).eval x) e ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t
          (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
          (state recordPorts middle false true false tail [])) :
    ∃ t ≤ stagedAttemptBudget base n m depth queryCost L, ∃ b,
      Eval (attempt (HashMassStaged.command query)) t d b ∧
      b.stacks = Function.update (Function.update d.stacks 768
        (HashGreedyCNF.entry clauses depth rows (CounterPrograms.value words.flatten)).payload) 769
        (HashGreedyCNF.entry clauses depth rows (CounterPrograms.value words.flatten)).score := by
  sorry

open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun
end
