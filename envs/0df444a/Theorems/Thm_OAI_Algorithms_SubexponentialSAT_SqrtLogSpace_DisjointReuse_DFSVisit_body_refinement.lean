-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSVisit_body_refinement
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.body_refinement
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:44:07.742995+00:00
-- url     : https://prove2.me/theorems/ae0df47c-3e29-4db9-94d4-8028d4e9640f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.body_refinement: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.body_refinement` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/DFSVisit.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/DFSVisit.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit`, with `open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement`):
--
--   ```lean
--   theorem body_refinement {k : ℕ} (threshold : List Bool) (leaf : Code)
--       (node : Node n) (rest : List (Node n)) (total parameterBound leafTime bound : ℕ) (d : Data)
--       (hk : 2 ≤ k) (hM : 2 ≤ BinaryArithmetic.toNat threshold)
--       (hv : Valid k node.formula) (hb : Boundary threshold ⟨node :: rest, total⟩ d)
--       (hdimension : BinaryArithmetic.toNat (d.stacks 264) = 4 * BinaryArithmetic.toNat threshold ^ (k - 1))
--       (hambient : BinaryArithmetic.toNat (d.stacks 267) = n)
--       (hparameterLength : (d.stacks 264).length ≤ parameterBound)
--       (hambientLength : (d.stacks 267).length ≤ n + 1)
--       (hcount : total + rawCount node.formula ≤ 2 ^ n)
--       (hbound : ∀ i, (d.stacks i).length ≤ bound)
--       (hpop : n + 1 + (pendingBytes rest).length +
--         11 * (SparseCountProgram.encodeBody node.formula).length + 13 ≤ bound)
--       (hselect : (SparsePriorityProgram.Selector.selectorCoefficient k + 24) *
--         SparseSelectorRefinement.inputVolume node.formula threshold ^ 4 ≤ bound)
--       (hbranch : (pendingBytes rest).length + (n + 1) +
--         620001 * (4 * (SparseCountProgram.encodeBody node.formula).length + 3) ^ 2 ≤ bound)
--       (hadd : 100 * (n + 1) ≤ bound)
--       (hleaf : LeafContract (n := n) k threshold parameterBound leaf leafTime bound) :
--       ∃ next t, t ≤ visitTime k n (SparseCountProgram.encodeBody node.formula).length
--           threshold.length leafTime bound ∧
--         ∃ e, BoundedEval (body k leaf) t d e bound ∧
--           Transition k (BinaryArithmetic.toNat threshold) ⟨node :: rest, total⟩ next ∧
--           Boundary threshold next e ∧
--           (∀ i, i ∈ ([256, 264, 266, 267] : List (Fin 1220)) → e.stacks i = d.stacks i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.selectorCoefficient` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.visitTime` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.rawCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.encodeBody`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Frontier`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Node`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Transition`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Valid`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.pendingBytes` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement.inputVolume` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.BoundedEval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.LeafContract`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Boundary` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.body` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative.normalized_loop` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/DFSVisit.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.body_refinement)

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

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement

variable {n : ℕ}

set_option maxHeartbeats 3200000 in
theorem body_refinement {k : ℕ} (threshold : List Bool) (leaf : Code)
    (node : Node n) (rest : List (Node n)) (total parameterBound leafTime bound : ℕ) (d : Data)
    (hk : 2 ≤ k) (hM : 2 ≤ BinaryArithmetic.toNat threshold)
    (hv : Valid k node.formula) (hb : Boundary threshold ⟨node :: rest, total⟩ d)
    (hdimension : BinaryArithmetic.toNat (d.stacks 264) = 4 * BinaryArithmetic.toNat threshold ^ (k - 1))
    (hambient : BinaryArithmetic.toNat (d.stacks 267) = n)
    (hparameterLength : (d.stacks 264).length ≤ parameterBound)
    (hambientLength : (d.stacks 267).length ≤ n + 1)
    (hcount : total + rawCount node.formula ≤ 2 ^ n)
    (hbound : ∀ i, (d.stacks i).length ≤ bound)
    (hpop : n + 1 + (pendingBytes rest).length +
      11 * (SparseCountProgram.encodeBody node.formula).length + 13 ≤ bound)
    (hselect : (SparsePriorityProgram.Selector.selectorCoefficient k + 24) *
      SparseSelectorRefinement.inputVolume node.formula threshold ^ 4 ≤ bound)
    (hbranch : (pendingBytes rest).length + (n + 1) +
      620001 * (4 * (SparseCountProgram.encodeBody node.formula).length + 3) ^ 2 ≤ bound)
    (hadd : 100 * (n + 1) ≤ bound)
    (hleaf : LeafContract (n := n) k threshold parameterBound leaf leafTime bound) :
    ∃ next t, t ≤ visitTime k n (SparseCountProgram.encodeBody node.formula).length
        threshold.length leafTime bound ∧
      ∃ e, BoundedEval (body k leaf) t d e bound ∧
        Transition k (BinaryArithmetic.toNat threshold) ⟨node :: rest, total⟩ next ∧
        Boundary threshold next e ∧
        (∀ i, i ∈ ([256, 264, 266, 267] : List (Fin 1220)) → e.stacks i = d.stacks i) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit
end
