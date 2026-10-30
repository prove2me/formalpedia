-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_LeafPreparationBudgets_prepared_common_bound_polynomial
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.prepared_common_bound_polynomial
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:58:20.001349+00:00
-- url     : https://prove2.me/theorems/0c28adbe-184c-433e-aaac-b124d6e93052
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.prepared_common_bound_polynomial: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.prepared_common_bound_polynomial` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/LeafPreparationBudgets.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/LeafPreparationBudgets.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets`, with `open SqrtLog SqrtLog.LeafOuterProgram NativeLeafPreparation NativeCodeAssembly`):
--
--   ```lean
--   theorem prepared_common_bound_polynomial :
--       ∃ C degree : ℕ, ∀ n m B W : ℕ, 0 < n → 0 < m → 0 < B → m ≤ n * B →
--         let L := W + NativeLeafSetup.canonicalStartTime n m W
--         ∀ a prepared : StructuredCalls.State 40 896, (∀ i, (a.stacks i).length ≤ L) →
--         LeafOuterProgram.Metadata m B prepared →
--         (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
--           (a.stacks 782).length (a.stacks 786).length) →
--         max (max (L + 1) (continuationSpace m B L a prepared))
--           (NativeLeafRun.commonBound n m B (retainedBound m B L a prepared)) ≤
--             C * (n + m + B + W + 16) ^ degree
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.canonicalStartTime` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.commonBound` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Metadata` (definitions bundle `OAIQ081S108` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.continuationSpace`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.retainedBound` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameterTime` (definitions bundle `OAIQ081S172` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.chosen_loaded_local_space` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.prepared_loaded` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/LeafPreparationBudgets.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.prepared_common_bound_polynomial)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S172

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets
open SqrtLog SqrtLog.LeafOuterProgram NativeLeafPreparation NativeCodeAssembly

theorem prepared_common_bound_polynomial :
    ∃ C degree : ℕ, ∀ n m B W : ℕ, 0 < n → 0 < m → 0 < B → m ≤ n * B →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared : StructuredCalls.State 40 896, (∀ i, (a.stacks i).length ≤ L) →
      LeafOuterProgram.Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      max (max (L + 1) (continuationSpace m B L a prepared))
        (NativeLeafRun.commonBound n m B (retainedBound m B L a prepared)) ≤
          C * (n + m + B + W + 16) ^ degree := by
  sorry

open SqrtLog.CodeSetupCost

open Filter SqrtLog.Asymptotic SqrtLog.Statement
open scoped Topology

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets
end
