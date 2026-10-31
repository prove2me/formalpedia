-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafContract_uniform_contract
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.uniform_contract
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:31:23.866637+00:00
-- url     : https://prove2.me/theorems/e27b3508-757c-4c8e-8e4b-cdaf0682dbe1
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.uniform_contract: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.uniform_contract` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract`, with `open BitProgram StructuredCalls DisjointReuse DFSVisit SparseDFSRefinement`, `open SqrtLog Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem uniform_contract (k parameterCoefficient parameterDegree : ℕ) (hk : 2 ≤ k) :
--       ∃ Cs spaceDegree : ℕ, ∃ Ct At : ℝ, ∃ timeDegree cutoff : ℕ,
--         1 ≤ Ct ∧ 1 ≤ At ∧ 1 ≤ timeDegree ∧
--         ∀ n inputLength parameterBound bound : ℕ, cutoff ≤ n → n ≤ inputLength →
--         parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree →
--         ∀ threshold : List Bool,
--         BinaryArithmetic.toNat threshold = SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) →
--         Cs * (inputLength + 1) ^ spaceDegree ≤ bound →
--         101 * SparseCountProgram.formulaBound n k + 103 ≤ bound → 5 * n + 6 ≤ bound →
--         LeafContract (n := n) k threshold parameterBound (NativeLeafProgram.command k)
--           (time n k (Nat.ceil (SqrtLog.Statement.runtimeBound Ct At timeDegree inputLength n)) bound)
--           bound
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.formulaBound` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sparsifySchedule` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.time` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseM` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.LeafContract` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafProgram.command` (definitions bundle `OAIQ081S193` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeBound` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.uniform_contract)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S193

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
open BitProgram StructuredCalls DisjointReuse DFSVisit SparseDFSRefinement

open SqrtLog Filter
open scoped Topology

theorem uniform_contract (k parameterCoefficient parameterDegree : ℕ) (hk : 2 ≤ k) :
    ∃ Cs spaceDegree : ℕ, ∃ Ct At : ℝ, ∃ timeDegree cutoff : ℕ,
      1 ≤ Ct ∧ 1 ≤ At ∧ 1 ≤ timeDegree ∧
      ∀ n inputLength parameterBound bound : ℕ, cutoff ≤ n → n ≤ inputLength →
      parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree →
      ∀ threshold : List Bool,
      BinaryArithmetic.toNat threshold = SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) →
      Cs * (inputLength + 1) ^ spaceDegree ≤ bound →
      101 * SparseCountProgram.formulaBound n k + 103 ≤ bound → 5 * n + 6 ≤ bound →
      LeafContract (n := n) k threshold parameterBound (NativeLeafProgram.command k)
        (time n k (Nat.ceil (SqrtLog.Statement.runtimeBound Ct At timeDegree inputLength n)) bound)
        bound := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
end
