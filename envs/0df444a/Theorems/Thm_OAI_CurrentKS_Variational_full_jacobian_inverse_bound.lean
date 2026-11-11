-- Prove2me | Theorems.Thm_OAI_CurrentKS_Variational_full_jacobian_inverse_bound
-- name    : OAI.CurrentKS.Variational.full_jacobian_inverse_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:55:43.67713+00:00
-- url     : https://prove2.me/theorems/32185f37-8eb0-4363-b3f0-1f1c0c7d4696
-- title:
--   OAI.CurrentKS.Variational.full_jacobian_inverse_bound: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.Variational`, with `open Matrix`, `open CurrentKS.Hermitian Matrix Set`, `open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius`):
--
--   ```lean
--   theorem full_jacobian_inverse_bound [NeZero d] (X Y P Q : H d)
--       (η : H d →L[ℝ] H d) (hηpos : ∀ A ∈ psdCone d,η A ∈ psdCone d)
--       (hηsym : SymmetricMap η) (hX : X ∈ pd d) (hY : Y ∈ pd d)
--       (hP : P ∈ pd d) (hQ : Q ∈ pd d) {ε : ℝ} (hε : 0 < ε)
--       (htr : _root_.OAI.CurrentKS.Hermitian.realTrace P+_root_.OAI.CurrentKS.Hermitian.realTrace Q=1)
--       (hStatX : sandwich (invH X) P = η Q+ε • (Hermitian.one : H d))
--       (hStatY : sandwich (invH Y) Q = η P+ε • (Hermitian.one : H d))
--       (hXlo : (200:ℝ)⁻¹ • (Hermitian.one : H d) ≤ X)
--       (hYlo : (200:ℝ)⁻¹ • (Hermitian.one : H d) ≤ Y)
--       (hXhi : X ≤ (100/ε) • (Hermitian.one : H d))
--       (hYhi : Y ≤ (100/ε) • (Hermitian.one : H d)) :
--       ∃ J : Vars d ≃L[ℝ] Vars d,
--         (∀ v,J v = CurrentKS.KKT.jacobian (identityPair d)
--           (onPairHilbert (linConstraint X Y η)) (hessian X Y P Q) v) ∧
--         ‖J.symm.toContinuousLinearMap‖ ≤ 10^18*((d : ℝ)+1)*(1+ε⁻¹)^4
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.Hermitian.H`, `OAI.CurrentKS.Hermitian.Mat`, `OAI.CurrentKS.Hermitian.instFiniteDimensionalRealSubtypeMatMemSubmoduleH`, `OAI.CurrentKS.Hermitian.invH`, `OAI.CurrentKS.Hermitian.matrixRealInnerProduct`, `OAI.CurrentKS.Hermitian.one`, `OAI.CurrentKS.Hermitian.pd`, `OAI.CurrentKS.Hermitian.psdCone`, `OAI.CurrentKS.Hermitian.realTrace`, `OAI.CurrentKS.Hermitian.sandwich`, `OAI.CurrentKS.KKT.Variables`, `OAI.CurrentKS.KKT.jacobian`, `OAI.CurrentKS.Variational.PairHilbert`, `OAI.CurrentKS.Variational.SymmetricMap`, `OAI.CurrentKS.Variational.Vars`, `OAI.CurrentKS.Variational.hessian`, `OAI.CurrentKS.Variational.identityPair`, `OAI.CurrentKS.Variational.linConstraint` and `OAI.CurrentKS.Variational.onPairHilbert` (definitions bundle `OAIQ241TT002` of this split); `OAI.CurrentKS.Variational.instNormedAddCommGroupPairHilbert`, `OAI.CurrentKS.Variational.instNormedSpaceRealVars_1` and `OAI.CurrentKS.Variational.instTopologicalSpaceVars` (definitions bundle `OAIQ241TT006` of this split).
--
--   **Used by.** The proof of `OAI.CurrentKS.State.value_strip_derivatives` of this split imports it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ241TT006

section

attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupPairHilbert_p1
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealPairHilbert_p1
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpacePairHilbert_p1
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupVars_1_p1
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealVars_1_p1
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceVars_p2
theorem full_jacobian_inverse_bound [NeZero d] (X Y P Q : H d)
    (η : H d →L[ℝ] H d) (hηpos : ∀ A ∈ psdCone d,η A ∈ psdCone d)
    (hηsym : SymmetricMap η) (hX : X ∈ pd d) (hY : Y ∈ pd d)
    (hP : P ∈ pd d) (hQ : Q ∈ pd d) {ε : ℝ} (hε : 0 < ε)
    (htr : _root_.OAI.CurrentKS.Hermitian.realTrace P+_root_.OAI.CurrentKS.Hermitian.realTrace Q=1)
    (hStatX : sandwich (invH X) P = η Q+ε • (Hermitian.one : H d))
    (hStatY : sandwich (invH Y) Q = η P+ε • (Hermitian.one : H d))
    (hXlo : (200:ℝ)⁻¹ • (Hermitian.one : H d) ≤ X)
    (hYlo : (200:ℝ)⁻¹ • (Hermitian.one : H d) ≤ Y)
    (hXhi : X ≤ (100/ε) • (Hermitian.one : H d))
    (hYhi : Y ≤ (100/ε) • (Hermitian.one : H d)) :
    ∃ J : Vars d ≃L[ℝ] Vars d,
      (∀ v,J v = CurrentKS.KKT.jacobian (identityPair d)
        (onPairHilbert (linConstraint X Y η)) (hessian X Y P Q) v) ∧
      ‖J.symm.toContinuousLinearMap‖ ≤ 10^18*((d : ℝ)+1)*(1+ε⁻¹)^4 := by
  sorry

end
end CurrentKS.Variational

end OAI
end
