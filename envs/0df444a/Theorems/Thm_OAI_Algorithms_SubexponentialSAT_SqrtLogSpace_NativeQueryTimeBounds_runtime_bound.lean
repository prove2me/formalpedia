-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeQueryTimeBounds_runtime_bound
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds.runtime_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:32:03.978979+00:00
-- url     : https://prove2.me/theorems/fb8861f0-1240-4a26-94e2-c7443a56de39
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds.runtime_bound: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds.runtime_bound` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeQueryTimeBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeQueryTimeBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds`, with `open SqrtLog SqrtLog.Statement CostAssembly.Polynomial NativeQueryInputBounds`):
--
--   ```lean
--   theorem runtime_bound (k qi ql recordDegree Cp dp Cn dn Cl dl Cf df C0 d0 : ℕ) :
--       ∃ C E : ℝ, ∃ degree cutoff : ℕ, 1 ≤ C ∧ 1 ≤ E ∧ 1 ≤ degree ∧
--         ∀ n ≥ cutoff, ∀ N L : ℕ, n ≤ N → L ≤ C0*(N+1)^d0 →
--         ∀ r : CostAssembly.Resources, CostAssembly.Bounds qi ql recordDegree n r →
--         ∀ f t d Q J h : ℕ,
--         let S := sourceCap Cn dn Cl dl N L k
--         let F := frontendCap Cf df L k
--         let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
--         let A := 12*P+4*N+6
--         let T := A+S+2
--         let cost := Cp*(S+f+1)^dp
--         let loop := HighQueryCorrect.loopBudget n h t d Q J A T
--           (CostAssembly.assembledWork k n r)
--         f ≤ F → t ≤ S → d ≤ S → Q ≤ S → J ≤ S → h ≤ n → h = r.branchVars →
--         (HighQueryCorrect.markedBudget F (S+f) cost loop (QueryHeadBudgets.compact A) : ℝ) ≤
--           runtimeBound C E degree N n ∧
--         (HighQueryCorrect.acceptedBudget F (S+f) cost loop (QueryHeadBudgets.compact A) : ℝ) ≤
--           runtimeBound C E degree N n
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Resources` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.acceptedBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.markedBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds.frontendCap`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds.preparedCap`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds.sourceCap` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.compact` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Bounds` (definitions bundle `OAIQ081S029` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.loopBudget` (definitions bundle `OAIQ081S183` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeBound` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeQueryTimeBounds.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds.runtime_bound)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S183

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds

open SqrtLog SqrtLog.Statement CostAssembly.Polynomial NativeQueryInputBounds

theorem runtime_bound (k qi ql recordDegree Cp dp Cn dn Cl dl Cf df C0 d0 : ℕ) :
    ∃ C E : ℝ, ∃ degree cutoff : ℕ, 1 ≤ C ∧ 1 ≤ E ∧ 1 ≤ degree ∧
      ∀ n ≥ cutoff, ∀ N L : ℕ, n ≤ N → L ≤ C0*(N+1)^d0 →
      ∀ r : CostAssembly.Resources, CostAssembly.Bounds qi ql recordDegree n r →
      ∀ f t d Q J h : ℕ,
      let S := sourceCap Cn dn Cl dl N L k
      let F := frontendCap Cf df L k
      let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
      let A := 12*P+4*N+6
      let T := A+S+2
      let cost := Cp*(S+f+1)^dp
      let loop := HighQueryCorrect.loopBudget n h t d Q J A T
        (CostAssembly.assembledWork k n r)
      f ≤ F → t ≤ S → d ≤ S → Q ≤ S → J ≤ S → h ≤ n → h = r.branchVars →
      (HighQueryCorrect.markedBudget F (S+f) cost loop (QueryHeadBudgets.compact A) : ℝ) ≤
        runtimeBound C E degree N n ∧
      (HighQueryCorrect.acceptedBudget F (S+f) cost loop (QueryHeadBudgets.compact A) : ℝ) ≤
        runtimeBound C E degree N n := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds
end
