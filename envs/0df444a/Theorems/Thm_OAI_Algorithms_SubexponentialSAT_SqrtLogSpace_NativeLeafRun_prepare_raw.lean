-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafRun_prepare_raw
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.prepare_raw
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:14:51.645149+00:00
-- url     : https://prove2.me/theorems/b42b7841-1e2c-46d1-b578-d84abc33f2be
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.prepare_raw: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.prepare_raw` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafRun.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafRun.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun`, with `open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram`, `open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound`, `open HashMassAdapter HashGreedyExecution`):
--
--   ```lean
--   theorem prepare_raw {n B W : ℕ} (F : DisjointReuse.RawCNF n) (a : State 40 896)
--       (ha : ∀ i, (a.stacks i).length ≤ W)
--       (hempty : ∀ i, i ≠ 784 → i ≠ 785 → i ≠ 786 → a.stacks i = [])
--       (hformula : a.stacks 784 = DisjointReuse.SparseCountProgram.encodeBody F)
--       (hm : F ≠ []) (hB : 0 < B)
--       (hn : BinaryArithmetic.toNat (a.stacks 785) = n)
--       (hBword : BinaryArithmetic.toNat (a.stacks 786) = B) :
--       ∃ (steps : ℕ) (started prepared out : State 40 896)
--         (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B),
--         let L := W + NativeLeafSetup.canonicalStartTime n F.length W
--         steps ≤ NativeLeafSetup.canonicalStartTime n F.length W +
--           NativeLeafPreparation.continuationTime F.length B L started prepared ∧
--         Eval NativeLeafPreparation.command steps a out ∧
--         (∀ i, (started.stacks i).length ≤ L) ∧
--         BinaryArithmetic.toNat (started.stacks 782) = F.length ∧
--         BinaryArithmetic.toNat (started.stacks 768) = 3 * F.length ∧
--         LeafOuterProgram.Metadata F.length B prepared ∧
--         (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime F.length B L
--           (started.stacks 782).length (started.stacks 786).length) ∧
--         NativeLeafPreparation.Ready n F.length B (HashGreedyCode.initial shifts Q) out ∧
--         WalshExistence.Good (SparseCode.gapDenom F.length B) shifts ∧
--         SparseCode.HasDistance Q (SparseCode.degree F.length B /
--           (100 * B * SparseCode.logSize F.length) + 1) ∧
--         (∀ i : Fin 896, 784 ≤ i.val → (i.val < 800 ∨ 818 < i.val) → out.stacks i = a.stacks i) ∧
--         (∀ i, (out.stacks i).length ≤ NativeLeafPreparation.retainedBound F.length B L started prepared) ∧
--         (∀ k c, k ≤ steps → Trace (compiled NativeLeafPreparation.command 784 788) k
--           (a.withPC (some (compiled NativeLeafPreparation.command 784 788).entry)) c →
--           ∀ i, (c.stacks i).length ≤ max (L + 1)
--             (NativeLeafPreparation.continuationSpace F.length B L started prepared)) ∧
--         ∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
--           out.stacks i = []
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNF.Clause` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.degree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.dimension`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.gapDenom`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.localRows` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.logSize` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedShifts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.Good` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.canonicalStartTime` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.HasDistance` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RawCNF` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.encodeBody` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.initial` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Metadata` (definitions bundle `OAIQ081S108` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.Ready` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.continuationSpace`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.continuationTime`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.retainedBound` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameterTime` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.command` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.prepared_loaded` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafRun.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.prepare_raw)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound
open HashMassAdapter HashGreedyExecution

theorem prepare_raw {n B W : ℕ} (F : DisjointReuse.RawCNF n) (a : State 40 896)
    (ha : ∀ i, (a.stacks i).length ≤ W)
    (hempty : ∀ i, i ≠ 784 → i ≠ 785 → i ≠ 786 → a.stacks i = [])
    (hformula : a.stacks 784 = DisjointReuse.SparseCountProgram.encodeBody F)
    (hm : F ≠ []) (hB : 0 < B)
    (hn : BinaryArithmetic.toNat (a.stacks 785) = n)
    (hBword : BinaryArithmetic.toNat (a.stacks 786) = B) :
    ∃ (steps : ℕ) (started prepared out : State 40 896)
      (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B),
      let L := W + NativeLeafSetup.canonicalStartTime n F.length W
      steps ≤ NativeLeafSetup.canonicalStartTime n F.length W +
        NativeLeafPreparation.continuationTime F.length B L started prepared ∧
      Eval NativeLeafPreparation.command steps a out ∧
      (∀ i, (started.stacks i).length ≤ L) ∧
      BinaryArithmetic.toNat (started.stacks 782) = F.length ∧
      BinaryArithmetic.toNat (started.stacks 768) = 3 * F.length ∧
      LeafOuterProgram.Metadata F.length B prepared ∧
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime F.length B L
        (started.stacks 782).length (started.stacks 786).length) ∧
      NativeLeafPreparation.Ready n F.length B (HashGreedyCode.initial shifts Q) out ∧
      WalshExistence.Good (SparseCode.gapDenom F.length B) shifts ∧
      SparseCode.HasDistance Q (SparseCode.degree F.length B /
        (100 * B * SparseCode.logSize F.length) + 1) ∧
      (∀ i : Fin 896, 784 ≤ i.val → (i.val < 800 ∨ 818 < i.val) → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ NativeLeafPreparation.retainedBound F.length B L started prepared) ∧
      (∀ k c, k ≤ steps → Trace (compiled NativeLeafPreparation.command 784 788) k
        (a.withPC (some (compiled NativeLeafPreparation.command 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ max (L + 1)
          (NativeLeafPreparation.continuationSpace F.length B L started prepared)) ∧
      ∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
        out.stacks i = [] := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
end
