-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSRefinement_popCurrent_boundary
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.popCurrent_boundary
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:03:29.236991+00:00
-- url     : https://prove2.me/theorems/a5ebcb1d-53f2-4ae1-b772-f77804d1a64a
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.popCurrent_boundary: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.popCurrent_boundary` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/CountDFS.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/CountDFS.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement`, with `open SAT SparsePriorityProgram BitProgram StructuredCalls`, `open SparseDFSProgram`):
--
--   ```lean
--   theorem popCurrent_boundary (threshold : List Bool) (node : Node n)
--       (rest : List (Node n)) (total : ℕ) (d : Data) (bound : ℕ)
--       (hb : Boundary threshold ⟨node :: rest, total⟩ d)
--       (hbound : ∀ i, (d.stacks i).length ≤ bound) :
--       ∃ e, Eval popCurrent (9 * (SparseCountProgram.encodeBody node.formula).length + 11) d e ∧
--         e.stacks 265 = SparseCountProgram.encodeBody node.formula ∧
--         e.stacks 257 = pendingBytes rest ∧
--         (∀ i, i ≠ 265 → i ≠ 257 → e.stacks i = d.stacks i) ∧
--         (∀ i, i.val < 256 → e.stacks i = []) ∧
--         e.regs 0 = false ∧ e.regs 1 = false ∧ e.regs 2 = true ∧
--         ∀ prefixSteps c,
--           prefixSteps ≤ 9 * (SparseCountProgram.encodeBody node.formula).length + 11 →
--           Trace (compiled popCurrent 256 256) prefixSteps
--             (d.withPC (some (compiled popCurrent 256 256).entry)) c →
--           ∀ i, (c.stacks i).length ≤ max
--             (n + 1 + (pendingBytes rest).length +
--               11 * (SparseCountProgram.encodeBody node.formula).length + 13) bound
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.encodeBody`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Node`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.pendingBytes` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Frontier` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.popCurrent` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Boundary` (definitions bundle `OAIQ081S099` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.body_refinement` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/CountDFS.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.popCurrent_boundary)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S099

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement

open SAT SparsePriorityProgram BitProgram StructuredCalls

variable {n : ℕ}

open SparseDFSProgram

theorem popCurrent_boundary (threshold : List Bool) (node : Node n)
    (rest : List (Node n)) (total : ℕ) (d : Data) (bound : ℕ)
    (hb : Boundary threshold ⟨node :: rest, total⟩ d)
    (hbound : ∀ i, (d.stacks i).length ≤ bound) :
    ∃ e, Eval popCurrent (9 * (SparseCountProgram.encodeBody node.formula).length + 11) d e ∧
      e.stacks 265 = SparseCountProgram.encodeBody node.formula ∧
      e.stacks 257 = pendingBytes rest ∧
      (∀ i, i ≠ 265 → i ≠ 257 → e.stacks i = d.stacks i) ∧
      (∀ i, i.val < 256 → e.stacks i = []) ∧
      e.regs 0 = false ∧ e.regs 1 = false ∧ e.regs 2 = true ∧
      ∀ prefixSteps c,
        prefixSteps ≤ 9 * (SparseCountProgram.encodeBody node.formula).length + 11 →
        Trace (compiled popCurrent 256 256) prefixSteps
          (d.withPC (some (compiled popCurrent 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ max
          (n + 1 + (pendingBytes rest).length +
            11 * (SparseCountProgram.encodeBody node.formula).length + 13) bound := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement
end
