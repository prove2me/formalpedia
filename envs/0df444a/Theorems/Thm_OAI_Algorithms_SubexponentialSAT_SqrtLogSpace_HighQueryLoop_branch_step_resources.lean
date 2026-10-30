-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryLoop_branch_step_resources
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.branch_step_resources
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:26:31.861221+00:00
-- url     : https://prove2.me/theorems/267baa37-7977-4838-98fb-875afaf7ee8b
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.branch_step_resources: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.branch_step_resources` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryLoop.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryLoop.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop`, with `open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram`, `open HighQueryAdapter PreparedBranchCount ProgramTapeReplay`, `open scoped BigOperators`, `open HashGreedyProgram.NativeRound`):
--
--   ```lean
--   theorem branch_step_resources {n : ℕ} (H : Finset (Fin n))
--       (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
--       (clause : List (SAT.Literal (Fin n))) (rank : ℕ) (hr : rank < 2 ^ H.card)
--       (a middle : Data) (querySteps L B D K : ℕ)
--       (he : Eval QueryStreamProgram.command querySteps (copiedHighCounter a) middle)
--       (hs : StageSpace QueryStreamProgram.command querySteps (copiedHighCounter a) K)
--       (hacc : BinaryArithmetic.toNat (a.stacks 788) =
--         rankSum (rankValue H hashes marked clause) 0 rank)
--       (hlen : (a.stacks 788).length ≤ n+1)
--       (hnext : middle.stacks 323 = countWord (rankValue H hashes marked clause rank))
--       (htmp : a.stacks 791 = [])
--       (hD : ∀ i, (a.stacks i).length ≤ D)
--       (h330 : (a.stacks 330).length ≤ L) (h792 : (a.stacks 792).length ≤ L)
--       (h789 : (a.stacks 789).length ≤ L)
--       (hwidth : n+1 ≤ B)
--       (hboundary : ∀ i, i ≠ 788 → i ≠ 323 → i ≠ 791 → (middle.stacks i).length ≤ B) :
--       ∃ steps b, Eval HighQueryProgram.branch steps a b ∧
--         steps ≤ querySteps + 11*L + 16*(n+2) + 15 ∧
--         BinaryArithmetic.toNat (b.stacks 788) =
--           rankSum (rankValue H hashes marked clause) 0 (rank+1) ∧
--         (b.stacks 788).length ≤ n+1 ∧ b.stacks 323=[] ∧ b.stacks 791=[] ∧
--         b.stacks 789=a.stacks 789 ∧ b.stacks 790=a.stacks 790 ∧
--         b.regs 21=true ∧ (∀ i, (b.stacks i).length ≤ B) ∧
--         StageSpace HighQueryProgram.branch (steps+1) a (max (max D K) (20*(n+2)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram.rankSum` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SparseRow` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount.rankValue` (definitions bundle `OAIQ081S127` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.StageSpace` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.copiedHighCounter` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.branch` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.command` (definitions bundle `OAIQ081S193` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.SAT.Literal` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryLoop.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.branch_step_resources)

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

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop

open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram
open HighQueryAdapter PreparedBranchCount ProgramTapeReplay
open scoped BigOperators

open HashGreedyProgram.NativeRound

theorem branch_step_resources {n : ℕ} (H : Finset (Fin n))
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (rank : ℕ) (hr : rank < 2 ^ H.card)
    (a middle : Data) (querySteps L B D K : ℕ)
    (he : Eval QueryStreamProgram.command querySteps (copiedHighCounter a) middle)
    (hs : StageSpace QueryStreamProgram.command querySteps (copiedHighCounter a) K)
    (hacc : BinaryArithmetic.toNat (a.stacks 788) =
      rankSum (rankValue H hashes marked clause) 0 rank)
    (hlen : (a.stacks 788).length ≤ n+1)
    (hnext : middle.stacks 323 = countWord (rankValue H hashes marked clause rank))
    (htmp : a.stacks 791 = [])
    (hD : ∀ i, (a.stacks i).length ≤ D)
    (h330 : (a.stacks 330).length ≤ L) (h792 : (a.stacks 792).length ≤ L)
    (h789 : (a.stacks 789).length ≤ L)
    (hwidth : n+1 ≤ B)
    (hboundary : ∀ i, i ≠ 788 → i ≠ 323 → i ≠ 791 → (middle.stacks i).length ≤ B) :
    ∃ steps b, Eval HighQueryProgram.branch steps a b ∧
      steps ≤ querySteps + 11*L + 16*(n+2) + 15 ∧
      BinaryArithmetic.toNat (b.stacks 788) =
        rankSum (rankValue H hashes marked clause) 0 (rank+1) ∧
      (b.stacks 788).length ≤ n+1 ∧ b.stacks 323=[] ∧ b.stacks 791=[] ∧
      b.stacks 789=a.stacks 789 ∧ b.stacks 790=a.stacks 790 ∧
      b.regs 21=true ∧ (∀ i, (b.stacks i).length ≤ B) ∧
      StageSpace HighQueryProgram.branch (steps+1) a (max (max D K) (20*(n+2))) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop
end
