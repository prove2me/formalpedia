-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryLoop_add_rank
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.add_rank
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:47:49.897174+00:00
-- url     : https://prove2.me/theorems/983870c5-13cb-4365-b044-aea2beb3d625
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.add_rank: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.add_rank` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryLoop.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryLoop.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop`, with `open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram`, `open HighQueryAdapter PreparedBranchCount ProgramTapeReplay`, `open scoped BigOperators`):
--
--   ```lean
--   theorem add_rank {n : ℕ} (H : Finset (Fin n))
--       (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
--       (clause : List (SAT.Literal (Fin n))) (rank : ℕ) (hr : rank < 2 ^ H.card)
--       (a : Data) (hacc : BinaryArithmetic.toNat (a.stacks 788) =
--         rankSum (rankValue H hashes marked clause) 0 rank)
--       (hlen : (a.stacks 788).length ≤ n+1)
--       (hnext : a.stacks 323 = countWord (rankValue H hashes marked clause rank))
--       (hscratch : a.stacks 791 = []) :
--       ∃ steps rf, steps ≤ 16*(n+2)+3 ∧
--         let b := Mass.state highPorts.mass a rf
--           (BinaryArithmetic.add (a.stacks 788) (a.stacks 323)) []
--         Eval (Mass.invoke highPorts.mass) steps a b ∧
--         b.stacks 323 = [] ∧ b.stacks 791 = [] ∧
--         (b.stacks 788).length ≤ n+1 ∧
--         BinaryArithmetic.toNat (b.stacks 788) =
--           rankSum (rankValue H hashes marked clause) 0 (rank+1) ∧
--         (∀ i, i ≠ 788 → i ≠ 323 → i ≠ 791 → b.stacks i = a.stacks i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.add` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram.rankSum` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Mass.invoke` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SparseRow` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Mass.state` (definitions bundle `OAIQ081S059` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram.Ports` (definitions bundle `OAIQ081S107` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount.rankValue` (definitions bundle `OAIQ081S127` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.highPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.Data` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.SAT.Literal` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.branch_step_resources` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryLoop.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.add_rank)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S127
import Definitions.Def_OAIQ081S136

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

theorem add_rank {n : ℕ} (H : Finset (Fin n))
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (rank : ℕ) (hr : rank < 2 ^ H.card)
    (a : Data) (hacc : BinaryArithmetic.toNat (a.stacks 788) =
      rankSum (rankValue H hashes marked clause) 0 rank)
    (hlen : (a.stacks 788).length ≤ n+1)
    (hnext : a.stacks 323 = countWord (rankValue H hashes marked clause rank))
    (hscratch : a.stacks 791 = []) :
    ∃ steps rf, steps ≤ 16*(n+2)+3 ∧
      let b := Mass.state highPorts.mass a rf
        (BinaryArithmetic.add (a.stacks 788) (a.stacks 323)) []
      Eval (Mass.invoke highPorts.mass) steps a b ∧
      b.stacks 323 = [] ∧ b.stacks 791 = [] ∧
      (b.stacks 788).length ≤ n+1 ∧
      BinaryArithmetic.toNat (b.stacks 788) =
        rankSum (rankValue H hashes marked clause) 0 (rank+1) ∧
      (∀ i, i ≠ 788 → i ≠ 323 → i ≠ 791 → b.stacks i = a.stacks i) := by
  sorry

open HashGreedyProgram.NativeRound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop
end
