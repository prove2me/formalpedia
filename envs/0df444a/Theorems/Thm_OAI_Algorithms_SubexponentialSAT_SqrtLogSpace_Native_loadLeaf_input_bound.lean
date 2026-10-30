-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_loadLeaf_input_bound
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.loadLeaf_input_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:04:00.446065+00:00
-- url     : https://prove2.me/theorems/3f54388a-6b83-4c7e-921b-f18c5a5dfac0
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.loadLeaf_input_bound: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.loadLeaf_input_bound` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeaf.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeaf.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native`, with `open BitProgram StructuredCalls`):
--
--   ```lean
--   theorem loadLeaf_input_bound {n k parameterBound B : ℕ} (threshold : List Bool)
--       (F : DisjointReuse.RawCNF n) (a : State 80 1220)
--       (hv : DisjointReuse.SparseDFSRefinement.Valid k F)
--       (hr : DisjointReuse.DFSVisit.LeafReady k threshold parameterBound F a)
--       (ha : ∀ i, (a.stacks i).length ≤ B) :
--       ∃ steps b, steps ≤ 1815 * B + 2746 ∧
--         DisjointReuse.DFSVisit.BoundedEval loadLeaf steps a b B ∧
--         b.stacks 1104 = DisjointReuse.SparseCountProgram.encodeBody F ∧
--         BinaryArithmetic.toNat (b.stacks 1105) = n ∧
--         BinaryArithmetic.toNat (b.stacks 1106) =
--           4 * BinaryArithmetic.toNat threshold ^ (k - 1) ∧
--         (∀ j : Fin 896, (b.stacks (ABI.leafStacks j)).length ≤
--           DisjointReuse.SparseCountProgram.formulaBound n k + (n + 1) + parameterBound) ∧
--         (∀ j : Fin 896, j ≠ 784 → j ≠ 785 → j ≠ 786 →
--           b.stacks (ABI.leafStacks j) = []) ∧
--         (∀ j, b.regs (ABI.leafRegisters j) = false) ∧
--         (∀ i, (¬ ∃ j, ABI.leafStacks j = i) → i ≠ 1219 → b.stacks i = a.stacks i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI.leafRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI.leafStacks` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.formulaBound` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RawCNF`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.encodeBody` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Valid` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.loadLeaf`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.BoundedEval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.LeafReady` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.Data` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.uniform_contract` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeaf.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.loadLeaf_input_bound)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S099

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

theorem loadLeaf_input_bound {n k parameterBound B : ℕ} (threshold : List Bool)
    (F : DisjointReuse.RawCNF n) (a : State 80 1220)
    (hv : DisjointReuse.SparseDFSRefinement.Valid k F)
    (hr : DisjointReuse.DFSVisit.LeafReady k threshold parameterBound F a)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, steps ≤ 1815 * B + 2746 ∧
      DisjointReuse.DFSVisit.BoundedEval loadLeaf steps a b B ∧
      b.stacks 1104 = DisjointReuse.SparseCountProgram.encodeBody F ∧
      BinaryArithmetic.toNat (b.stacks 1105) = n ∧
      BinaryArithmetic.toNat (b.stacks 1106) =
        4 * BinaryArithmetic.toNat threshold ^ (k - 1) ∧
      (∀ j : Fin 896, (b.stacks (ABI.leafStacks j)).length ≤
        DisjointReuse.SparseCountProgram.formulaBound n k + (n + 1) + parameterBound) ∧
      (∀ j : Fin 896, j ≠ 784 → j ≠ 785 → j ≠ 786 →
        b.stacks (ABI.leafStacks j) = []) ∧
      (∀ j, b.regs (ABI.leafRegisters j) = false) ∧
      (∀ i, (¬ ∃ j, ABI.leafStacks j = i) → i ≠ 1219 → b.stacks i = a.stacks i) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end
