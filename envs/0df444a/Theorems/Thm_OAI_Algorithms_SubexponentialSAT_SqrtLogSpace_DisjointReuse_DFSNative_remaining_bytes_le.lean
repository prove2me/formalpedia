-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSNative_remaining_bytes_le
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative.remaining_bytes_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:51:01.638249+00:00
-- url     : https://prove2.me/theorems/d2d0b206-35f9-43e4-96b6-8fc2667062e4
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative.remaining_bytes_le: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative.remaining_bytes_le` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/DFSNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/DFSNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative`, with `open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement DFSVisit`):
--
--   ```lean
--   theorem remaining_bytes_le {k M visits total : ℕ} (F : RawCNF n)
--       (node : Node n) (rest : List (Node n)) (hM : 2 ≤ M)
--       (hwidth : ∀ C ∈ F, C.length ≤ k)
--       (htrace : Transitions k M visits
--         ⟨[⟨ExecCNF.normalize SAT.Literal.negate F, 0⟩], 0⟩ ⟨node :: rest, total⟩) :
--       (pendingBytes rest).length ≤ SparseDFSBoundarySpace.frontierBound
--         (SparseCountProgram.formulaBound n k) (F.length * k)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.ExecCNF.Clause`, `OAI.Algorithms.SubexponentialSAT.ExecCNF.normalize` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal.negate` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.formulaBound` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSBoundarySpace.frontierBound` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RawCNF`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Node`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Transitions`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.pendingBytes` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Frontier` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative.normalized_loop` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/DFSNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative.remaining_bytes_le)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S064

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement DFSVisit
variable {n : ℕ}

theorem remaining_bytes_le {k M visits total : ℕ} (F : RawCNF n)
    (node : Node n) (rest : List (Node n)) (hM : 2 ≤ M)
    (hwidth : ∀ C ∈ F, C.length ≤ k)
    (htrace : Transitions k M visits
      ⟨[⟨ExecCNF.normalize SAT.Literal.negate F, 0⟩], 0⟩ ⟨node :: rest, total⟩) :
    (pendingBytes rest).length ≤ SparseDFSBoundarySpace.frontierBound
      (SparseCountProgram.formulaBound n k) (F.length * k) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative
end
