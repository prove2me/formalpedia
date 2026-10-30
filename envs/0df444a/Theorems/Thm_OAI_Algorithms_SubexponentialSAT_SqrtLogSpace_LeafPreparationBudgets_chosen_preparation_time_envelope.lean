-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_LeafPreparationBudgets_chosen_preparation_time_envelope
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.chosen_preparation_time_envelope
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:56:35.657676+00:00
-- url     : https://prove2.me/theorems/a7a44573-ccdb-4899-b19d-28638086d543
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.chosen_preparation_time_envelope: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.chosen_preparation_time_envelope` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/LeafPreparationBudgets.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/LeafPreparationBudgets.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets`, with `open SqrtLog SqrtLog.LeafOuterProgram NativeLeafPreparation NativeCodeAssembly`, `open SqrtLog.CodeSetupCost`):
--
--   ```lean
--   theorem chosen_preparation_time_envelope (k wordCoefficient wordDegree : ℕ) :
--       ∃ C degree : ℕ, ∀ n inputLength m W H wordCap : ℕ,
--         0 < m → n ≤ inputLength → 1 ≤ sparsifySchedule n →
--         let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
--           (sparsifySchedule n) (by omega) ^ (k - 1)
--         m ≤ n * B → W ≤ wordCoefficient * (inputLength + 1) ^ wordDegree →
--         let L := W + NativeLeafSetup.canonicalStartTime n m W
--         ∀ a prepared : Data, (∀ i, (a.stacks i).length ≤ L) →
--         Metadata m B prepared →
--         (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
--           (a.stacks 782).length (a.stacks 786).length) →
--         SparseCode.localRows m B ≤ H → SparseCode.degree m B ≤ H →
--         SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ H →
--         SparseCode.dimension m B ≤ H →
--         (prepared.stacks 800).length ≤ wordCap →
--         (prepared.stacks 801).length ≤ wordCap →
--         NativeLeafSetup.canonicalStartTime n m W + continuationTime m B L a prepared ≤
--           C * (inputLength + envelope 3000000000000 H wordCap + 1) ^ degree
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.degree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.dimension`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.localRows` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.logSize` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupCost.envelope` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sparsifySchedule` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.canonicalStartTime` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseM` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Data` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Metadata` (definitions bundle `OAIQ081S108` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.continuationTime` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameterTime` (definitions bundle `OAIQ081S172` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.prepared_loaded` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/LeafPreparationBudgets.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.chosen_preparation_time_envelope)

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

open SqrtLog.CodeSetupCost

theorem chosen_preparation_time_envelope (k wordCoefficient wordDegree : ℕ) :
    ∃ C degree : ℕ, ∀ n inputLength m W H wordCap : ℕ,
      0 < m → n ≤ inputLength → 1 ≤ sparsifySchedule n →
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
        (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B → W ≤ wordCoefficient * (inputLength + 1) ^ wordDegree →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared : Data, (∀ i, (a.stacks i).length ≤ L) →
      Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      SparseCode.localRows m B ≤ H → SparseCode.degree m B ≤ H →
      SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ H →
      SparseCode.dimension m B ≤ H →
      (prepared.stacks 800).length ≤ wordCap →
      (prepared.stacks 801).length ≤ wordCap →
      NativeLeafSetup.canonicalStartTime n m W + continuationTime m B L a prepared ≤
        C * (inputLength + envelope 3000000000000 H wordCap + 1) ^ degree := by
  sorry

open Filter SqrtLog.Asymptotic SqrtLog.Statement
open scoped Topology

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets
end
