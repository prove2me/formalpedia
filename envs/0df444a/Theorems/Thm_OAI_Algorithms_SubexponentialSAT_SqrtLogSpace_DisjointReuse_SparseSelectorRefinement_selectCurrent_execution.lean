-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseSelectorRefinement_selectCurrent_execution
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement.selectCurrent_execution
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:45:21.326186+00:00
-- url     : https://prove2.me/theorems/09e52ef4-c1a5-4874-a396-1fe4f5a91cc5
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement.selectCurrent_execution: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement.selectCurrent_execution` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparseSelectorRefinement.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparseSelectorRefinement.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement`, with `open BitProgram StructuredCalls SparseDFSProgram SparsePriorityProgram`):
--
--   ```lean
--   theorem selectCurrent_execution {k : ℕ} (F : RawCNF n) (base : List Bool)
--       (d : Data) (frameBound : ℕ) (hk : 2 ≤ k) (hM : 2 ≤ BinaryArithmetic.toNat base)
--       (hwidth : ∀ C ∈ F, C.length ≤ k) (hnodup : ∀ C ∈ F, C.Nodup)
--       (hdistinct : (F.map ExecCNF.clauseSet).Nodup)
--       (hF : d.stacks 265 = SparseCountProgram.encodeBody F) (hbase : d.stacks 259 = base)
--       (hclean : ∀ i : Fin 1220, i.val < 24 → d.stacks i = [])
--       (hbound : ∀ i, (d.stacks i).length ≤ frameBound) :
--       ∃ t ≤ Selector.selectorCoefficient k * inputVolume F base ^ 4 + 1, ∃ e : Data,
--         Eval (selectCurrent k) t d e ∧
--         (∀ i : Fin 1220, i ≠ 9 → i ≠ 12 → e.stacks i = d.stacks i) ∧
--         (e.regs 23 = false → e.stacks = d.stacks ∧ e.stacks 9 = [] ∧ e.stacks 12 = [] ∧
--           SparsePriority.select (ExecCNF.formulaSet F) (BinaryArithmetic.toNat base) = none ∧
--           (∀ c H, (c, H) ∈ rawCandidates k F → 0 < H.length → H.length < c →
--             (selectedRaw F c H).length < BinaryArithmetic.toNat base ^ (c - H.length)) ∧
--           ∀ v, SAT.occurrences v (ExecCNF.formulaSet F) ≤
--             4 * BinaryArithmetic.toNat base ^ (k - 1)) ∧
--         (e.regs 23 = true → ∃ c H,
--           RawPriority k F (BinaryArithmetic.toNat base) c H ∧
--           SparsePriority.Priority (ExecCNF.formulaSet F) (BinaryArithmetic.toNat base) c
--             (ExecCNF.clauseSet H) ∧
--           e.stacks 9 = ExecCoreChildProgram.clauseCode (H.map Encoding.literalCode) ∧
--           e.stacks 12 = SparseCountProgram.encodeBody (selectedRaw F c H)) ∧
--         (∀ prefixSteps intermediate, prefixSteps ≤ t →
--           Trace (compiled (selectCurrent k) 256 256) prefixSteps
--             (d.withPC (some (compiled (selectCurrent k) 256 256).entry)) intermediate →
--           ∀ i, (intermediate.stacks i).length ≤
--             max ((Selector.selectorCoefficient k + 24) * inputVolume F base ^ 4) frameBound)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNF.Clause`, `OAI.Algorithms.SubexponentialSAT.ExecCNF.clauseSet` and `OAI.Algorithms.SubexponentialSAT.ExecCNF.formulaSet` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.selectorCoefficient` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.clauseCode` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.occurrences` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.RawPriority`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.rawCandidates` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.selectedRaw` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RawCNF`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.encodeBody`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriority.Priority`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriority.select` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement.inputVolume` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.Data` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.selectCurrent` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.literalCode`, `OAI.Algorithms.SubexponentialSAT.SAT.Clause` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.body_refinement` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparseSelectorRefinement.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement.selectCurrent_execution)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement

open BitProgram StructuredCalls SparseDFSProgram SparsePriorityProgram

variable {n : ℕ}

theorem selectCurrent_execution {k : ℕ} (F : RawCNF n) (base : List Bool)
    (d : Data) (frameBound : ℕ) (hk : 2 ≤ k) (hM : 2 ≤ BinaryArithmetic.toNat base)
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hnodup : ∀ C ∈ F, C.Nodup)
    (hdistinct : (F.map ExecCNF.clauseSet).Nodup)
    (hF : d.stacks 265 = SparseCountProgram.encodeBody F) (hbase : d.stacks 259 = base)
    (hclean : ∀ i : Fin 1220, i.val < 24 → d.stacks i = [])
    (hbound : ∀ i, (d.stacks i).length ≤ frameBound) :
    ∃ t ≤ Selector.selectorCoefficient k * inputVolume F base ^ 4 + 1, ∃ e : Data,
      Eval (selectCurrent k) t d e ∧
      (∀ i : Fin 1220, i ≠ 9 → i ≠ 12 → e.stacks i = d.stacks i) ∧
      (e.regs 23 = false → e.stacks = d.stacks ∧ e.stacks 9 = [] ∧ e.stacks 12 = [] ∧
        SparsePriority.select (ExecCNF.formulaSet F) (BinaryArithmetic.toNat base) = none ∧
        (∀ c H, (c, H) ∈ rawCandidates k F → 0 < H.length → H.length < c →
          (selectedRaw F c H).length < BinaryArithmetic.toNat base ^ (c - H.length)) ∧
        ∀ v, SAT.occurrences v (ExecCNF.formulaSet F) ≤
          4 * BinaryArithmetic.toNat base ^ (k - 1)) ∧
      (e.regs 23 = true → ∃ c H,
        RawPriority k F (BinaryArithmetic.toNat base) c H ∧
        SparsePriority.Priority (ExecCNF.formulaSet F) (BinaryArithmetic.toNat base) c
          (ExecCNF.clauseSet H) ∧
        e.stacks 9 = ExecCoreChildProgram.clauseCode (H.map Encoding.literalCode) ∧
        e.stacks 12 = SparseCountProgram.encodeBody (selectedRaw F c H)) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ t →
        Trace (compiled (selectCurrent k) 256 256) prefixSteps
          (d.withPC (some (compiled (selectCurrent k) 256 256).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          max ((Selector.selectorCoefficient k + 24) * inputVolume F base ^ 4) frameBound) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement
end
