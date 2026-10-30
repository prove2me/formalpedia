-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafPreparation_afterCanonical_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.afterCanonical_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:14:41.034126+00:00
-- url     : https://prove2.me/theorems/62444e78-b3af-4016-b613-3763403de7d8
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.afterCanonical_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.afterCanonical_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafPreparation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafPreparation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation`, with `open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram`, `open HashGreedyProgram`):
--
--   ```lean
--   theorem afterCanonical_eval (a : Data) {n m B L : ℕ}
--       (hm : 0 < m) (hB : 0 < B) (he : WorkerEmpty a)
--       (ha : ∀ i, (a.stacks i).length ≤ L)
--       (hc : BinaryArithmetic.toNat (a.stacks 782) = m)
--       (hBword : BinaryArithmetic.toNat (a.stacks 786) = B)
--       (hwidth : a.stacks 768 = a.stacks 780)
--       (hmod : BinaryArithmetic.toNat (a.stacks 780) = 3 * m)
--       (hmodlen : (a.stacks 780).length = HashCandidates.digitWidth m)
--       (h783 : a.stacks 783 = a.stacks 780)
--       (hdepth : BinaryArithmetic.toNat (a.stacks 817) = SparseCode.distanceDenom m B)
--       (hrounds : a.stacks 781 = List.replicate (HashSelect.loopCap n m) true) :
--       ∃ (steps : ℕ) (prepared out : Data)
--         (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B),
--         let P := NativeLeafSetup.parameterTime m B L (a.stacks 782).length (a.stacks 786).length
--         let A := L + P
--         let R := NativeCodeAssembly.afterBoundary A m B
--           (prepared.stacks 801) (a.stacks 782) (a.stacks 768)
--         steps ≤ P + NativeCodeAssembly.afterTime A m B (prepared.stacks 800).length
--           (prepared.stacks 801) (a.stacks 782) (a.stacks 768) +
--             finishTime (SparseCode.distanceDenom m B) R ∧
--         Eval afterCanonical steps a out ∧
--         Metadata m B prepared ∧ (∀ i, (prepared.stacks i).length ≤ A) ∧
--         Ready n m B (HashGreedyCode.initial shifts Q) out ∧
--         WalshExistence.Good (SparseCode.gapDenom m B) shifts ∧
--         SparseCode.HasDistance Q (SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1) ∧
--         (∀ i : Fin 896, 784 ≤ i.val → (i.val < 800 ∨ 818 < i.val) →
--           out.stacks i = a.stacks i) ∧
--         (∀ i, (out.stacks i).length ≤ max R
--           (2 * (SparseCode.distanceDenom m B * HashCandidates.digitWidth m) + 3)) ∧
--         ∀ k c, k ≤ steps → Trace (compiled afterCanonical 784 788) k
--           (a.withPC (some (compiled afterCanonical 784 788).entry)) c →
--           ∀ i, (c.stacks i).length ≤
--             max (max (A + 1) (NativeCodeAssembly.afterSpace A m B
--               (prepared.stacks 800).length (prepared.stacks 801) (a.stacks 782) (a.stacks 768)))
--               (R + finishTime (SparseCode.distanceDenom m B) R)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.degree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.dimension`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.gapDenom`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.localRows` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.logSize` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.finishTime` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedShifts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.Good` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.digitWidth`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.afterBoundary` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.afterSpace` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.HasDistance` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.afterTime` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.initial` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Data` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Metadata` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.WorkerEmpty` (definitions bundle `OAIQ081S108` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.Ready` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameterTime` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.afterCanonical` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.prepare_raw` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafPreparation.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.afterCanonical_eval)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram
open HashGreedyProgram

theorem afterCanonical_eval (a : Data) {n m B L : ℕ}
    (hm : 0 < m) (hB : 0 < B) (he : WorkerEmpty a)
    (ha : ∀ i, (a.stacks i).length ≤ L)
    (hc : BinaryArithmetic.toNat (a.stacks 782) = m)
    (hBword : BinaryArithmetic.toNat (a.stacks 786) = B)
    (hwidth : a.stacks 768 = a.stacks 780)
    (hmod : BinaryArithmetic.toNat (a.stacks 780) = 3 * m)
    (hmodlen : (a.stacks 780).length = HashCandidates.digitWidth m)
    (h783 : a.stacks 783 = a.stacks 780)
    (hdepth : BinaryArithmetic.toNat (a.stacks 817) = SparseCode.distanceDenom m B)
    (hrounds : a.stacks 781 = List.replicate (HashSelect.loopCap n m) true) :
    ∃ (steps : ℕ) (prepared out : Data)
      (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B),
      let P := NativeLeafSetup.parameterTime m B L (a.stacks 782).length (a.stacks 786).length
      let A := L + P
      let R := NativeCodeAssembly.afterBoundary A m B
        (prepared.stacks 801) (a.stacks 782) (a.stacks 768)
      steps ≤ P + NativeCodeAssembly.afterTime A m B (prepared.stacks 800).length
        (prepared.stacks 801) (a.stacks 782) (a.stacks 768) +
          finishTime (SparseCode.distanceDenom m B) R ∧
      Eval afterCanonical steps a out ∧
      Metadata m B prepared ∧ (∀ i, (prepared.stacks i).length ≤ A) ∧
      Ready n m B (HashGreedyCode.initial shifts Q) out ∧
      WalshExistence.Good (SparseCode.gapDenom m B) shifts ∧
      SparseCode.HasDistance Q (SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1) ∧
      (∀ i : Fin 896, 784 ≤ i.val → (i.val < 800 ∨ 818 < i.val) →
        out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ max R
        (2 * (SparseCode.distanceDenom m B * HashCandidates.digitWidth m) + 3)) ∧
      ∀ k c, k ≤ steps → Trace (compiled afterCanonical 784 788) k
        (a.withPC (some (compiled afterCanonical 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤
          max (max (A + 1) (NativeCodeAssembly.afterSpace A m B
            (prepared.stacks 800).length (prepared.stacks 801) (a.stacks 782) (a.stacks 768)))
            (R + finishTime (SparseCode.distanceDenom m B) R) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation
end
