-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryJetSemantics_residual_group_diagonal_dense
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics.residual_group_diagonal_dense
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:33:47.45596+00:00
-- url     : https://prove2.me/theorems/7cae799a-7b03-4ba9-911d-211a82ef4ed8
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics.residual_group_diagonal_dense: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics.residual_group_diagonal_dense` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryJetSemantics.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryJetSemantics.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics`, with `open scoped BigOperators`, `open Polynomial OAI OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing`, `open LeafProgram LeafProgram.NodeSemantics`, `open IdempotentApplyProgram.Steps (Context)`, `open NodeConcrete MomentsProgram`):
--
--   ```lean
--   theorem residual_group_diagonal_dense (q : Factor.Spec r Q n d) (hu : q.u = q.p.t)
--       (H : Finset (Fin n)) (high : H → Bool) (state : Fin 768 → List Bool)
--       (x : ResidualEmbedding.Free H → Bool)
--       (hstate : ∀ v : Fin n, (state 145).getD v.val false = HighIncidence.glue H high x v)
--       (ids : List ℕ)
--       (hzero : ∀ id j (v : Fin n), v ∈ H →
--         PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0)
--       (hhash : ∀ id ∈ ids, ∀ hi : id < (AssignmentConcrete.weightedHashes q).length,
--         ∀ w ∈ (AssignmentConcrete.weightedHashes q)[id], ∀ l ∈ w.literals,
--           l.variable ∉ H → (l.variable.val, n + id) ∈ q.ps)
--       (hmark : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids →
--         ∀ l ∈ q.markedClause, l.variable ∉ H →
--           (l.variable.val, n + (AssignmentConcrete.weightedHashes q).length) ∈ q.ps) :
--       QueryEvaluation.specializeDense q.p.t q.J x
--         (Squarefree.canonical q.u q.J ((ids.map
--           (AssignmentConcrete.residualValue q.ctx (q.p.model.base q.p.t)
--             (RingBasis.basis (q.p.model.F q.p.t)) q.code
--             (residualJet q.p q.ps q.packing H high q.theta state)
--             (AssignmentConcrete.weightedHashes q) q.marked q.markedClause)).prod)) =
--         Dense.ofPolynomial q.p.t q.J ((ids.map
--           (selectedExpression q.p.t (codeDigits q.ctx (q.p.model.base q.p.t) q.code)
--             (decodedHashes q) q.marked q.markedClause
--             (fun id v => shift (q.p.ops.decode q.theta)
--               (branchPath H high (completedRows q.p q.ps q.packing H) x id v)))).prod)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree` and `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Support` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.glue` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbedding.Free` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.shift` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Jet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ZJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.canonical` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.instCommMonoidSupportOfDecidableEq` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingBasis.basis`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.base` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.branchPath` (definitions bundle `OAIQ081S059` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.selectedExpression` (definitions bundle `OAIQ081S076` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense.ofPolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEvaluation.specializeDense` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instCommSemiring` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.WeightedClause` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.ops` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete.residualValue` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.codeDigits` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete.weightedHashes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.decodedHashes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.ctx` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.markedClause` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.fixedSourceRow` (definitions bundle `OAIQ081S174` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.completedRows` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.residualJet` (definitions bundle `OAIQ081S181` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics.colored_residual_target_dense_shift` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryJetSemantics.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics.residual_group_diagonal_dense)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S181

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics

open scoped BigOperators
open Polynomial OAI OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open LeafProgram LeafProgram.NodeSemantics
open IdempotentApplyProgram.Steps (Context)

section NativeReadout

open NodeConcrete MomentsProgram

variable {r Q n d : ℕ} {G : Type*} [Fintype G] [DecidableEq G]

theorem residual_group_diagonal_dense (q : Factor.Spec r Q n d) (hu : q.u = q.p.t)
    (H : Finset (Fin n)) (high : H → Bool) (state : Fin 768 → List Bool)
    (x : ResidualEmbedding.Free H → Bool)
    (hstate : ∀ v : Fin n, (state 145).getD v.val false = HighIncidence.glue H high x v)
    (ids : List ℕ)
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0)
    (hhash : ∀ id ∈ ids, ∀ hi : id < (AssignmentConcrete.weightedHashes q).length,
      ∀ w ∈ (AssignmentConcrete.weightedHashes q)[id], ∀ l ∈ w.literals,
        l.variable ∉ H → (l.variable.val, n + id) ∈ q.ps)
    (hmark : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids →
      ∀ l ∈ q.markedClause, l.variable ∉ H →
        (l.variable.val, n + (AssignmentConcrete.weightedHashes q).length) ∈ q.ps) :
    QueryEvaluation.specializeDense q.p.t q.J x
      (Squarefree.canonical q.u q.J ((ids.map
        (AssignmentConcrete.residualValue q.ctx (q.p.model.base q.p.t)
          (RingBasis.basis (q.p.model.F q.p.t)) q.code
          (residualJet q.p q.ps q.packing H high q.theta state)
          (AssignmentConcrete.weightedHashes q) q.marked q.markedClause)).prod)) =
      Dense.ofPolynomial q.p.t q.J ((ids.map
        (selectedExpression q.p.t (codeDigits q.ctx (q.p.model.base q.p.t) q.code)
          (decodedHashes q) q.marked q.markedClause
          (fun id v => shift (q.p.ops.decode q.theta)
            (branchPath H high (completedRows q.p q.ps q.packing H) x id v)))).prod) := by
  sorry

end NativeReadout

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics
end
