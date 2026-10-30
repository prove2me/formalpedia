-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSCompletedTree_completed_visits_reciprocal
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree.completed_visits_reciprocal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:50:26.867693+00:00
-- url     : https://prove2.me/theorems/5d4a16d9-9461-41f8-ada4-5b71cff8c68b
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree.completed_visits_reciprocal: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree.completed_visits_reciprocal` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/DFSCompletedTree.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/DFSCompletedTree.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree`, with `open SparseDFSRefinement`):
--
--   ```lean
--   theorem completed_visits_reciprocal {F : RawCNF n} {visits total : ℕ}
--       (k s : ℕ) (hk : 2 ≤ k) (hs : 0 < s) (hv : Valid k F)
--       (h : Transitions k (SparseBudget.chooseM k 1 s (by decide)) visits
--         ⟨[⟨F, 0⟩], 0⟩ ⟨[], total⟩) :
--       (visits : ℝ) ≤
--         ((SparseCharging.depthConstant k (SparseBudget.chooseM k 1 s (by decide)) * n + 1 : ℕ) : ℝ) ^ 2 *
--           (2 : ℝ) ^ ((n : ℝ) / s)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCharging.depthConstant` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseM` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RawCNF`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Node`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Transitions`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Valid` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Frontier` (definitions bundle `OAIQ081S064` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_dfs_execution` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/DFSCompletedTree.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree.completed_visits_reciprocal)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S064

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree

open SparseDFSRefinement
variable {n : ℕ}

theorem completed_visits_reciprocal {F : RawCNF n} {visits total : ℕ}
    (k s : ℕ) (hk : 2 ≤ k) (hs : 0 < s) (hv : Valid k F)
    (h : Transitions k (SparseBudget.chooseM k 1 s (by decide)) visits
      ⟨[⟨F, 0⟩], 0⟩ ⟨[], total⟩) :
    (visits : ℝ) ≤
      ((SparseCharging.depthConstant k (SparseBudget.chooseM k 1 s (by decide)) * n + 1 : ℕ) : ℝ) ^ 2 *
        (2 : ℝ) ^ ((n : ℝ) / s) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree
end
