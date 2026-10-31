-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafContract_staged_rounds_time_hashCalls
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.staged_rounds_time_hashCalls
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:40:47.952845+00:00
-- url     : https://prove2.me/theorems/fd29aab9-4f10-4901-a22c-d5e12a6de174
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.staged_rounds_time_hashCalls: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.staged_rounds_time_hashCalls` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract`, with `open BitProgram StructuredCalls DisjointReuse DFSVisit SparseDFSRefinement`, `open SqrtLog HashGreedyProgram.NativeRound in`):
--
--   ```lean
--   theorem staged_rounds_time_hashCalls (factor power C d : ℕ) :
--       ∃ A degree : ℕ, ∀ {n m B R : ℕ} {initial : List (List Bool)} (base : State 40 896),
--         NativeLeafPreparation.Ready n m B initial base → 0 < m →
--         ∀ (queryCost : List Bool → ℕ) (inputLength newQuery oldQuery : ℕ),
--         (∀ i, (base.stacks i).length ≤ NativeLeafRun.commonBound n m B R) →
--         NativeLeafRun.commonBound n m B R ≤ C * (inputLength + 1) ^ d →
--         (∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ newQuery) →
--         newQuery ≤ factor * (oldQuery + inputLength + 1) ^ power →
--         NativeLeafRun.roundsTime base n m (SparseCode.distanceDenom m B) queryCost
--           (NativeLeafRun.commonBound n m B R) ≤
--           A * (CostAssembly.hashCalls n m (SparseCode.distanceDenom m B) +
--             oldQuery + inputLength + 1) ^ degree
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.hashCalls` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.commonBound` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.Ready` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.roundsTime` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_execution` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.staged_rounds_time_hashCalls)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
open BitProgram StructuredCalls DisjointReuse DFSVisit SparseDFSRefinement

open SqrtLog HashGreedyProgram.NativeRound in
theorem staged_rounds_time_hashCalls (factor power C d : ℕ) :
    ∃ A degree : ℕ, ∀ {n m B R : ℕ} {initial : List (List Bool)} (base : State 40 896),
      NativeLeafPreparation.Ready n m B initial base → 0 < m →
      ∀ (queryCost : List Bool → ℕ) (inputLength newQuery oldQuery : ℕ),
      (∀ i, (base.stacks i).length ≤ NativeLeafRun.commonBound n m B R) →
      NativeLeafRun.commonBound n m B R ≤ C * (inputLength + 1) ^ d →
      (∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ newQuery) →
      newQuery ≤ factor * (oldQuery + inputLength + 1) ^ power →
      NativeLeafRun.roundsTime base n m (SparseCode.distanceDenom m B) queryCost
        (NativeLeafRun.commonBound n m B R) ≤
        A * (CostAssembly.hashCalls n m (SparseCode.distanceDenom m B) +
          oldQuery + inputLength + 1) ^ degree := by
  sorry

open SqrtLog Filter
open scoped Topology

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
end
