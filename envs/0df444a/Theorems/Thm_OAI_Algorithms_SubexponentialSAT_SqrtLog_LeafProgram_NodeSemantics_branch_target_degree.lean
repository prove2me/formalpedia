-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_NodeSemantics_branch_target_degree
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.branch_target_degree
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:54:32.72333+00:00
-- url     : https://prove2.me/theorems/bbfd89cf-9433-44b3-a298-592f3919992d
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.branch_target_degree: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.branch_target_degree` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramNodeSemanticsSource.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramNodeSemanticsSource.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics`, with `open scoped BigOperators`, `open Polynomial`):
--
--   ```lean
--   theorem branch_target_degree (H : Finset V) (high : H → Bool)
--       (rows : ℕ → V → ResidualEmbedding.Free H → R[X]) (t k r : ℕ)
--       (hrows : ∀ i v w, (rows i v w).natDegree ≤ r)
--       (digits : Fin t → R[X]) (hdigits : ∀ s, (digits s).natDegree ≤ 2)
--       (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
--       (hwidth : ∀ ws ∈ hashes, ∀ w ∈ ws, w.2.length ≤ k) (hclause : clause.length ≤ k) :
--       (target H t digits hashes marked clause (branchPath H high rows)).natDegree ≤
--         Reconstruction.markedDegreeBound k r hashes.length t
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbedding.Free` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Reconstruction.markedDegreeBound` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SparseRow` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.branchPath` (definitions bundle `OAIQ081S059` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.target` (definitions bundle `OAIQ081S076` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.actual_target_degree` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramNodeSemanticsSource.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.branch_target_degree)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S020
import Definitions.Def_OAIQ081S076

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section

variable {R V : Type*} [CommRing R] [Fintype V] [DecidableEq V]

theorem branch_target_degree (H : Finset V) (high : H → Bool)
    (rows : ℕ → V → ResidualEmbedding.Free H → R[X]) (t k r : ℕ)
    (hrows : ∀ i v w, (rows i v w).natDegree ≤ r)
    (digits : Fin t → R[X]) (hdigits : ∀ s, (digits s).natDegree ≤ 2)
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (hwidth : ∀ ws ∈ hashes, ∀ w ∈ ws, w.2.length ≤ k) (hclause : clause.length ≤ k) :
    (target H t digits hashes marked clause (branchPath H high rows)).natDegree ≤
      Reconstruction.markedDegreeBound k r hashes.length t := by
  sorry

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end
