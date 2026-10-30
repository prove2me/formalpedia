-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_chosen_query_scalars_cutoff_of_scope_resources
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.chosen_query_scalars_cutoff_of_scope_resources
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:21:44.951733+00:00
-- url     : https://prove2.me/theorems/f62439ad-5af0-4913-beb1-3b6920ed410e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.chosen_query_scalars_cutoff_of_scope_resources: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.chosen_query_scalars_cutoff_of_scope_resources` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryParameterBudgets.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryParameterBudgets.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace`, with `open SqrtLog SqrtLog.Asymptotic SqrtLog.ProducedQueryResources in`):
--
--   ```lean
--   theorem chosen_query_scalars_cutoff_of_scope_resources (k : ℕ) (hk : 2 ≤ k) :
--       ∃ cutoff : ℕ, ∀ n ≥ cutoff,
--         20 ≤ n ∧ 2 ≤ sparsifySchedule n ∧
--         let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
--           (sparsifySchedule n) (by omega) ^ (k - 1)
--         ∀ q : LeafQueryFrontend.Query, q.Valid → ambient q = n →
--           0 < q.clauses.length → q.clauses.length ≤ n * B →
--           q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
--           HighIncidenceProgram.Prepare.mass q.scopeRows ≤
--             (3 * n * SparseCode.degreeBound q.clauses.length B +
--               (HashSelect.loopCap n q.clauses.length + 1) *
--                 SparseCode.distanceDenom q.clauses.length B + 1) * k →
--           (∀ row ∈ q.scopeRows, row.length ≤
--             (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k) →
--           ScanBounds q k (4 * k + 3) ∧ SmallInputs q k n
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.degreeBound` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.mass` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sparsifySchedule` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseM` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.scopeRows` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ambient` (definitions bundle `OAIQ081S171` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ScanBounds` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.SmallInputs` (definitions bundle `OAIQ081S178` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_numeric_caps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.trial_numeric_caps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.chosen_ofPacking_cutoff` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.chosen_scalar_input_cap_of_scope_resources` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryParameterBudgets.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.chosen_query_scalars_cutoff_of_scope_resources)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S178

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open SqrtLog SqrtLog.Asymptotic SqrtLog.ProducedQueryResources in
theorem chosen_query_scalars_cutoff_of_scope_resources (k : ℕ) (hk : 2 ≤ k) :
    ∃ cutoff : ℕ, ∀ n ≥ cutoff,
      20 ≤ n ∧ 2 ≤ sparsifySchedule n ∧
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
        (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ q : LeafQueryFrontend.Query, q.Valid → ambient q = n →
        0 < q.clauses.length → q.clauses.length ≤ n * B →
        q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
        HighIncidenceProgram.Prepare.mass q.scopeRows ≤
          (3 * n * SparseCode.degreeBound q.clauses.length B +
            (HashSelect.loopCap n q.clauses.length + 1) *
              SparseCode.distanceDenom q.clauses.length B + 1) * k →
        (∀ row ∈ q.scopeRows, row.length ≤
          (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k) →
        ScanBounds q k (4 * k + 3) ∧ SmallInputs q k n := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end
