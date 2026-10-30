-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeOuterBudgets_runtime_of_tree_and_leaf
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets.runtime_of_tree_and_leaf
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:43:57.621885+00:00
-- url     : https://prove2.me/theorems/7d3a6a64-a1f3-4703-8a76-278a18a4215f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets.runtime_of_tree_and_leaf: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets.runtime_of_tree_and_leaf` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeOuterBudgets.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeOuterBudgets.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets`, with `open OAI BitProgram StructuredCalls SqrtLog.Statement DisjointReuse`):
--
--   ```lean
--   theorem runtime_of_tree_and_leaf (k coefficient degree : ℕ)
--       (leafConstant leafExponent : ℝ) (hC : 1≤leafConstant) (hA : 0≤leafExponent)
--       (leafDegree : ℕ) :
--       ∃ C : ℝ, 1≤C ∧ ∀ n L visits leafTime primitiveTime : ℕ,
--         20 ≤ n → 1 ≤ sparsifySchedule n → n ≤ L →
--         (visits : ℝ)≤
--           ((SparseCharging.depthConstant k
--             (SparseBudget.chooseM k 1 (sparsifySchedule n) (by decide))*n+1 : ℕ) : ℝ)^2*
--             (2 : ℝ)^((n : ℝ)/sparsifySchedule n) →
--         (leafTime : ℝ) ≤ runtimeBound leafConstant leafExponent leafDegree L n →
--         primitiveTime ≤ coefficient*(L+1)^degree*(visits+1)*(leafTime+1) →
--         (primitiveTime : ℝ) ≤ runtimeBound C (256+leafExponent)
--           (degree+(4*(k-2)+2)+leafDegree) L n
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sparsifySchedule` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCharging.depthConstant` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseM` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeBound` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeOuterBudgets.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets.runtime_of_tree_and_leaf)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S043

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets
open OAI BitProgram StructuredCalls SqrtLog.Statement DisjointReuse

theorem runtime_of_tree_and_leaf (k coefficient degree : ℕ)
    (leafConstant leafExponent : ℝ) (hC : 1≤leafConstant) (hA : 0≤leafExponent)
    (leafDegree : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∀ n L visits leafTime primitiveTime : ℕ,
      20 ≤ n → 1 ≤ sparsifySchedule n → n ≤ L →
      (visits : ℝ)≤
        ((SparseCharging.depthConstant k
          (SparseBudget.chooseM k 1 (sparsifySchedule n) (by decide))*n+1 : ℕ) : ℝ)^2*
          (2 : ℝ)^((n : ℝ)/sparsifySchedule n) →
      (leafTime : ℝ) ≤ runtimeBound leafConstant leafExponent leafDegree L n →
      primitiveTime ≤ coefficient*(L+1)^degree*(visits+1)*(leafTime+1) →
      (primitiveTime : ℝ) ≤ runtimeBound C (256+leafExponent)
        (degree+(4*(k-2)+2)+leafDegree) L n := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets
end
