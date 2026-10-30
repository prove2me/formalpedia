-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyCode_supplied_trial_raw_resources
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_trial_raw_resources
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:18:26.130165+00:00
-- url     : https://prove2.me/theorems/8911ccd7-67ea-4fb3-8a81-7d383b4076c9
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_trial_raw_resources: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_trial_raw_resources` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyCode.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyCode.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode`, with `open SqrtLog`, `open scoped BigOperators`, `open HashGreedyCNF`):
--
--   ```lean
--   theorem supplied_trial_raw_resources {n m B : ℕ}
--       (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
--       (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
--       (rounds rank : ℕ) :
--       let rows := (HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) rank ::
--         history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds).map (raw m hm)
--       rows.length = SparseCode.totalRows m B + rounds + 1 ∧
--         LeafScopeResourceBounds.slots rows ≤
--           SparseCode.totalRows m B * SparseCode.degreeBound m B +
--             (rounds + 1) * SparseCode.distanceDenom m B ∧
--         ∀ row ∈ rows, row.length ≤ SparseCode.degreeBound m B + SparseCode.distanceDenom m B + 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.degreeBound` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.slots` (definitions bundle `OAIQ081S017` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedShifts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.totalRows` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.initial` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.raw` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate.candidate` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Clause` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.trial_envelope` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.trial_numeric_caps` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyCode.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_trial_raw_resources)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode

open SqrtLog
open scoped BigOperators
open HashGreedyCNF

noncomputable section

theorem supplied_trial_raw_resources {n m B : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (rounds rank : ℕ) :
    let rows := (HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) rank ::
      history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds).map (raw m hm)
    rows.length = SparseCode.totalRows m B + rounds + 1 ∧
      LeafScopeResourceBounds.slots rows ≤
        SparseCode.totalRows m B * SparseCode.degreeBound m B +
          (rounds + 1) * SparseCode.distanceDenom m B ∧
      ∀ row ∈ rows, row.length ≤ SparseCode.degreeBound m B + SparseCode.distanceDenom m B + 1 := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode
end
