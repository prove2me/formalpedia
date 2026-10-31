-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafContract_local_execution
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_execution
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:30:52.043079+00:00
-- url     : https://prove2.me/theorems/fa299cd3-4d67-41a6-9e45-0dd8c14f1a16
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_execution: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_execution` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract`, with `open BitProgram StructuredCalls DisjointReuse DFSVisit SparseDFSRefinement`, `open SqrtLog Filter`, `open scoped Topology`, `open SqrtLog HashGreedyProgram.NativeRound HashGreedyRound in`):
--
--   ```lean
--   theorem local_execution (k parameterCoefficient parameterDegree : ℕ) (hk : 2 ≤ k) :
--       ∃ Cs spaceDegree : ℕ, ∃ Ct At : ℝ, ∃ timeDegree cutoff : ℕ,
--         1 ≤ Ct ∧ 1 ≤ At ∧ 1 ≤ timeDegree ∧
--         ∀ n inputLength parameterBound : ℕ, cutoff ≤ n → n ≤ inputLength →
--         parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree →
--         let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
--         let W := SparseCountProgram.formulaBound n k + (n + 1) + parameterBound
--         ∀ (F : RawCNF n) (a : State 40 896), Valid k F → F ≠ [] → F.length ≤ n * B →
--         (∀ i, (a.stacks i).length ≤ W) →
--         (∀ i, i ≠ 784 → i ≠ 785 → i ≠ 786 → a.stacks i = []) →
--         a.stacks 784 = SparseCountProgram.encodeBody F →
--         BinaryArithmetic.toNat (a.stacks 785) = n →
--         BinaryArithmetic.toNat (a.stacks 786) = B →
--         ∃ steps ≤ Nat.ceil (Statement.runtimeBound Ct At timeDegree inputLength n), ∃ out,
--           Eval (NativeLeafProgram.localCommand k) steps a out ∧
--           out.stacks 788 = countWord (rawCount F) ∧
--           ∀ t z, t ≤ steps → Trace (NativeLeafProgram.localProgram k) t
--             (a.withPC (some (NativeLeafProgram.localProgram k).entry)) z →
--             ∀ i, (z.stacks i).length ≤ Cs * (inputLength + 1) ^ spaceDegree
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNF.Clause` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.formulaBound` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sparsifySchedule` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseM` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RawCNF`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.rawCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.encodeBody` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Valid` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafProgram.localCommand` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafProgram.localProgram` (definitions bundle `OAIQ081S193` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.SAT.Literal`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeBound` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.uniform_contract` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_execution)

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

open SqrtLog HashGreedyProgram.NativeRound HashGreedyRound in
theorem local_execution (k parameterCoefficient parameterDegree : ℕ) (hk : 2 ≤ k) :
    ∃ Cs spaceDegree : ℕ, ∃ Ct At : ℝ, ∃ timeDegree cutoff : ℕ,
      1 ≤ Ct ∧ 1 ≤ At ∧ 1 ≤ timeDegree ∧
      ∀ n inputLength parameterBound : ℕ, cutoff ≤ n → n ≤ inputLength →
      parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      let W := SparseCountProgram.formulaBound n k + (n + 1) + parameterBound
      ∀ (F : RawCNF n) (a : State 40 896), Valid k F → F ≠ [] → F.length ≤ n * B →
      (∀ i, (a.stacks i).length ≤ W) →
      (∀ i, i ≠ 784 → i ≠ 785 → i ≠ 786 → a.stacks i = []) →
      a.stacks 784 = SparseCountProgram.encodeBody F →
      BinaryArithmetic.toNat (a.stacks 785) = n →
      BinaryArithmetic.toNat (a.stacks 786) = B →
      ∃ steps ≤ Nat.ceil (Statement.runtimeBound Ct At timeDegree inputLength n), ∃ out,
        Eval (NativeLeafProgram.localCommand k) steps a out ∧
        out.stacks 788 = countWord (rawCount F) ∧
        ∀ t z, t ≤ steps → Trace (NativeLeafProgram.localProgram k) t
          (a.withPC (some (NativeLeafProgram.localProgram k).entry)) z →
          ∀ i, (z.stacks i).length ≤ Cs * (inputLength + 1) ^ spaceDegree := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
end
