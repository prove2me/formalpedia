-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_eventually_raw_scope_guards
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_raw_scope_guards
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:44:43.553784+00:00
-- url     : https://prove2.me/theorems/66f44f12-d9ad-4fa0-ab6f-e0c2562578f1
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_raw_scope_guards: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_raw_scope_guards` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryScopeBudgets.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryScopeBudgets.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace`, with `open Filter SqrtLog SqrtLog.Asymptotic SqrtLog.LeafStatisticsProgram`, `open SqrtLog.LeafScopeResourceBounds SqrtLog.CostAssembly`, `open scoped Topology`):
--
--   ```lean
--   theorem eventually_raw_scope_guards (k qi : ℕ) :
--       ∀ᶠ n : ℕ in atTop, ∀ (scopes : List (List ℕ)) (m B : ℕ),
--         0 < m → m ≤ n * B → B ≤ L n ^ qi →
--         scopes.length ≤ 3 * n + HashSelect.loopCap n m + 2 →
--         HighIncidenceProgram.Prepare.mass scopes ≤
--           (3 * n * SparseCode.degreeBound m B +
--             (HashSelect.loopCap n m + 1) * SparseCode.distanceDenom m B + 1) * k →
--         (∀ row ∈ scopes, row.length ≤
--           (SparseCode.degreeBound m B + SparseCode.distanceDenom m B + 1) * k) →
--         (∀ row ∈ scopes, row.Nodup) →
--         let mask := forwardHighMask scopes n (Nat.sqrt (L n) + 1)
--         let x := measuredParameterInput scopes mask m k
--         LeafParametersProgram.Guard x ∧ x.freeCount ≤ n ∧ n ≤ 2 * x.freeCount ∧
--           x.factors ≤ 4 * n + HashSelect.loopCap n m + 2 ∧
--           x.occurrence ≤ L x.freeCount ^ (resourceExponent qi + 1) ∧
--           x.arity ≤ L x.freeCount ^ (resourceExponent qi + 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.L` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.degreeBound` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Input` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.forwardHighMask` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.mass` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.resourceExponent` (definitions bundle `OAIQ081S017` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.measuredParameterInput` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` (definitions bundle `OAIQ081S037` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_scan_bounds_of_scope_resources` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryScopeBudgets.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_raw_scope_guards)

import Mathlib
import Definitions.Def_OAIQ081S017
import Definitions.Def_OAIQ081S030
import Definitions.Def_OAIQ081S037

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Filter SqrtLog SqrtLog.Asymptotic SqrtLog.LeafStatisticsProgram
open SqrtLog.LeafScopeResourceBounds SqrtLog.CostAssembly
open scoped Topology

theorem eventually_raw_scope_guards (k qi : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (scopes : List (List ℕ)) (m B : ℕ),
      0 < m → m ≤ n * B → B ≤ L n ^ qi →
      scopes.length ≤ 3 * n + HashSelect.loopCap n m + 2 →
      HighIncidenceProgram.Prepare.mass scopes ≤
        (3 * n * SparseCode.degreeBound m B +
          (HashSelect.loopCap n m + 1) * SparseCode.distanceDenom m B + 1) * k →
      (∀ row ∈ scopes, row.length ≤
        (SparseCode.degreeBound m B + SparseCode.distanceDenom m B + 1) * k) →
      (∀ row ∈ scopes, row.Nodup) →
      let mask := forwardHighMask scopes n (Nat.sqrt (L n) + 1)
      let x := measuredParameterInput scopes mask m k
      LeafParametersProgram.Guard x ∧ x.freeCount ≤ n ∧ n ≤ 2 * x.freeCount ∧
        x.factors ≤ 4 * n + HashSelect.loopCap n m + 2 ∧
        x.occurrence ≤ L x.freeCount ^ (resourceExponent qi + 1) ∧
        x.arity ≤ L x.freeCount ^ (resourceExponent qi + 1) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end
