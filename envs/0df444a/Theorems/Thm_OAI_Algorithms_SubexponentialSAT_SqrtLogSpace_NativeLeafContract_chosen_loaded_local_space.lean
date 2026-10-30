-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafContract_chosen_loaded_local_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.chosen_loaded_local_space
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:59:41.154057+00:00
-- url     : https://prove2.me/theorems/81f6afc3-4d9f-4d84-aee4-04bdba683c2e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.chosen_loaded_local_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.chosen_loaded_local_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract`, with `open BitProgram StructuredCalls DisjointReuse DFSVisit SparseDFSRefinement`):
--
--   ```lean
--   theorem chosen_loaded_local_space (k parameterCoefficient parameterDegree : ℕ) :
--       ∃ C degree : ℕ, ∀ n inputLength m parameterBound K : ℕ,
--         0 < n → 0 < m → n ≤ inputLength → 1 ≤ sparsifySchedule n →
--         parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree →
--         let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
--         m ≤ n * B →
--         let W := SparseCountProgram.formulaBound n k + (n + 1) + parameterBound
--         let startupBound := W + NativeLeafSetup.canonicalStartTime n m W
--         ∀ started prepared base : State 40 896,
--         (∀ i, (started.stacks i).length ≤ startupBound) →
--         SqrtLog.LeafOuterProgram.Metadata m B prepared →
--         (∀ i, (prepared.stacks i).length ≤ startupBound +
--           NativeLeafSetup.parameterTime m B startupBound
--             (started.stacks 782).length (started.stacks 786).length) →
--         CounterPrograms.value (base.stacks 782) = m →
--         (∀ i, (base.stacks i).length ≤
--           NativeLeafPreparation.retainedBound m B startupBound started prepared) →
--         let L := NativeLeafRun.commonBound n m B
--           (NativeLeafPreparation.retainedBound m B startupBound started prepared)
--         max (max (startupBound + 1)
--             (NativeLeafPreparation.continuationSpace m B startupBound started prepared))
--           (max (NativeLeafRun.roundsSpace base n m (SqrtLog.SparseCode.distanceDenom m B) L K)
--             (max K (1000 * L + 100))) ≤ max K (C * (inputLength + 1) ^ degree)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.CounterPrograms.value` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.formulaBound` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sparsifySchedule` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.canonicalStartTime` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseM` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.commonBound` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Metadata` (definitions bundle `OAIQ081S108` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.roundsSpace` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.continuationSpace`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.retainedBound` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameterTime` (definitions bundle `OAIQ081S172` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_execution` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.chosen_loaded_local_space)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S172

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
open BitProgram StructuredCalls DisjointReuse DFSVisit SparseDFSRefinement

theorem chosen_loaded_local_space (k parameterCoefficient parameterDegree : ℕ) :
    ∃ C degree : ℕ, ∀ n inputLength m parameterBound K : ℕ,
      0 < n → 0 < m → n ≤ inputLength → 1 ≤ sparsifySchedule n →
      parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B →
      let W := SparseCountProgram.formulaBound n k + (n + 1) + parameterBound
      let startupBound := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ started prepared base : State 40 896,
      (∀ i, (started.stacks i).length ≤ startupBound) →
      SqrtLog.LeafOuterProgram.Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ startupBound +
        NativeLeafSetup.parameterTime m B startupBound
          (started.stacks 782).length (started.stacks 786).length) →
      CounterPrograms.value (base.stacks 782) = m →
      (∀ i, (base.stacks i).length ≤
        NativeLeafPreparation.retainedBound m B startupBound started prepared) →
      let L := NativeLeafRun.commonBound n m B
        (NativeLeafPreparation.retainedBound m B startupBound started prepared)
      max (max (startupBound + 1)
          (NativeLeafPreparation.continuationSpace m B startupBound started prepared))
        (max (NativeLeafRun.roundsSpace base n m (SqrtLog.SparseCode.distanceDenom m B) L K)
          (max K (1000 * L + 100))) ≤ max K (C * (inputLength + 1) ^ degree) := by
  sorry

open SqrtLog Filter
open scoped Topology

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
end
