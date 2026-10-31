-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_eventually_scan_bounds_of_scope_resources
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_scan_bounds_of_scope_resources
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:22:15.593591+00:00
-- url     : https://prove2.me/theorems/b90edb73-73ca-4e09-8c62-7acebf63c4e7
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_scan_bounds_of_scope_resources: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_scan_bounds_of_scope_resources` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryParameterBudgets.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryParameterBudgets.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace`, with `open Filter SqrtLog SqrtLog.Asymptotic SqrtLog.ProducedQueryResources`):
--
--   ```lean
--   theorem eventually_scan_bounds_of_scope_resources (k qi : ℕ) :
--       ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B : ℕ), q.Valid → ambient q = n →
--         0 < q.clauses.length → q.clauses.length ≤ n * B → B ≤ L n ^ qi →
--         q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
--         HighIncidenceProgram.Prepare.mass q.scopeRows ≤
--           (3 * n * SparseCode.degreeBound q.clauses.length B +
--             (HashSelect.loopCap n q.clauses.length + 1) *
--               SparseCode.distanceDenom q.clauses.length B + 1) * k →
--         (∀ row ∈ q.scopeRows, row.length ≤
--           (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k) →
--         ScanBounds q k (resourceExponent qi + 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.L` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.degreeBound` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.mass` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.resourceExponent` (definitions bundle `OAIQ081S017` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.scopeRows` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ambient` (definitions bundle `OAIQ081S171` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ScanBounds` (definitions bundle `OAIQ081S178` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.chosen_query_scalars_cutoff_of_scope_resources` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryParameterBudgets.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_scan_bounds_of_scope_resources)

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

open Filter SqrtLog SqrtLog.Asymptotic SqrtLog.ProducedQueryResources
  SqrtLog.LeafQueryFrontend SqrtLog.LeafScopeResourceBounds in
theorem eventually_scan_bounds_of_scope_resources (k qi : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B : ℕ), q.Valid → ambient q = n →
      0 < q.clauses.length → q.clauses.length ≤ n * B → B ≤ L n ^ qi →
      q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
      HighIncidenceProgram.Prepare.mass q.scopeRows ≤
        (3 * n * SparseCode.degreeBound q.clauses.length B +
          (HashSelect.loopCap n q.clauses.length + 1) *
            SparseCode.distanceDenom q.clauses.length B + 1) * k →
      (∀ row ∈ q.scopeRows, row.length ≤
        (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k) →
      ScanBounds q k (resourceExponent qi + 1) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end
