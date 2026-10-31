-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafContract_prepared_loaded
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.prepared_loaded
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:14:48.838027+00:00
-- url     : https://prove2.me/theorems/25c53365-6ebb-4974-81e1-7a0f2bdb2de3
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.prepared_loaded: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.prepared_loaded` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract`, with `open BitProgram StructuredCalls DisjointReuse DFSVisit SparseDFSRefinement`, `open SqrtLog Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem prepared_loaded (k parameterCoefficient parameterDegree : ℕ) :
--       ∃ C degree : ℕ, ∃ Ct : ℝ, ∃ exponent timeDegree cutoff : ℕ, 1 ≤ Ct ∧
--         ∀ n inputLength parameterBound : ℕ, cutoff ≤ n → n ≤ inputLength →
--         parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree →
--         let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
--         let W := SparseCountProgram.formulaBound n k + (n + 1) + parameterBound
--         ∀ (F : RawCNF n) (a : State 40 896), F ≠ [] → F.length ≤ n * B →
--         (∀ i, (a.stacks i).length ≤ W) →
--         (∀ i, i ≠ 784 → i ≠ 785 → i ≠ 786 → a.stacks i = []) →
--         a.stacks 784 = SparseCountProgram.encodeBody F →
--         BinaryArithmetic.toNat (a.stacks 785) = n →
--         BinaryArithmetic.toNat (a.stacks 786) = B →
--         ∃ (steps : ℕ) (started prepared base : State 40 896)
--           (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B),
--           let startup := W + NativeLeafSetup.canonicalStartTime n F.length W
--           let R := NativeLeafPreparation.retainedBound F.length B startup started prepared
--           let L := NativeLeafRun.commonBound n F.length B R
--           Eval NativeLeafPreparation.command steps a base ∧
--           (steps : ℝ) ≤ Statement.runtimeBound Ct exponent timeDegree inputLength n ∧
--           (∀ i, (started.stacks i).length ≤ startup) ∧
--           LeafOuterProgram.Metadata F.length B prepared ∧
--           (∀ i, (prepared.stacks i).length ≤ startup +
--             NativeLeafSetup.parameterTime F.length B startup
--               (started.stacks 782).length (started.stacks 786).length) ∧
--           NativeLeafPreparation.Ready n F.length B (HashGreedyCode.initial shifts Q) base ∧
--           WalshExistence.Good (SparseCode.gapDenom F.length B) shifts ∧
--           SparseCode.HasDistance Q (SparseCode.degree F.length B /
--             (100 * B * SparseCode.logSize F.length) + 1) ∧
--           base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) ∧
--           BinaryArithmetic.toNat (base.stacks 785) = n ∧
--           (∀ i, (base.stacks i).length ≤ R) ∧
--           (∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
--             base.stacks i = []) ∧
--           L ≤ C * (inputLength + 1) ^ degree ∧
--           ∀ t z, t ≤ steps → Trace (compiled NativeLeafPreparation.command 784 788) t
--             (a.withPC (some (compiled NativeLeafPreparation.command 784 788).entry)) z →
--             ∀ i, (z.stacks i).length ≤ C * (inputLength + 1) ^ degree
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNF.Clause` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.degree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.dimension`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.gapDenom`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.localRows` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.logSize` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.formulaBound` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sparsifySchedule` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedShifts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.Good` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.canonicalStartTime` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseM` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.HasDistance` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RawCNF`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.commonBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.clauseRecords` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.encodeBody` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.initial` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Metadata` (definitions bundle `OAIQ081S108` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.Ready` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.retainedBound` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameterTime` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.command` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList`, `OAI.Algorithms.SubexponentialSAT.SAT.Literal` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeBound` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_execution` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.prepared_loaded)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178

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

theorem prepared_loaded (k parameterCoefficient parameterDegree : ℕ) :
    ∃ C degree : ℕ, ∃ Ct : ℝ, ∃ exponent timeDegree cutoff : ℕ, 1 ≤ Ct ∧
      ∀ n inputLength parameterBound : ℕ, cutoff ≤ n → n ≤ inputLength →
      parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      let W := SparseCountProgram.formulaBound n k + (n + 1) + parameterBound
      ∀ (F : RawCNF n) (a : State 40 896), F ≠ [] → F.length ≤ n * B →
      (∀ i, (a.stacks i).length ≤ W) →
      (∀ i, i ≠ 784 → i ≠ 785 → i ≠ 786 → a.stacks i = []) →
      a.stacks 784 = SparseCountProgram.encodeBody F →
      BinaryArithmetic.toNat (a.stacks 785) = n →
      BinaryArithmetic.toNat (a.stacks 786) = B →
      ∃ (steps : ℕ) (started prepared base : State 40 896)
        (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B),
        let startup := W + NativeLeafSetup.canonicalStartTime n F.length W
        let R := NativeLeafPreparation.retainedBound F.length B startup started prepared
        let L := NativeLeafRun.commonBound n F.length B R
        Eval NativeLeafPreparation.command steps a base ∧
        (steps : ℝ) ≤ Statement.runtimeBound Ct exponent timeDegree inputLength n ∧
        (∀ i, (started.stacks i).length ≤ startup) ∧
        LeafOuterProgram.Metadata F.length B prepared ∧
        (∀ i, (prepared.stacks i).length ≤ startup +
          NativeLeafSetup.parameterTime F.length B startup
            (started.stacks 782).length (started.stacks 786).length) ∧
        NativeLeafPreparation.Ready n F.length B (HashGreedyCode.initial shifts Q) base ∧
        WalshExistence.Good (SparseCode.gapDenom F.length B) shifts ∧
        SparseCode.HasDistance Q (SparseCode.degree F.length B /
          (100 * B * SparseCode.logSize F.length) + 1) ∧
        base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) ∧
        BinaryArithmetic.toNat (base.stacks 785) = n ∧
        (∀ i, (base.stacks i).length ≤ R) ∧
        (∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
          base.stacks i = []) ∧
        L ≤ C * (inputLength + 1) ^ degree ∧
        ∀ t z, t ≤ steps → Trace (compiled NativeLeafPreparation.command 784 788) t
          (a.withPC (some (compiled NativeLeafPreparation.command 784 788).entry)) z →
          ∀ i, (z.stacks i).length ≤ C * (inputLength + 1) ^ degree := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
end
