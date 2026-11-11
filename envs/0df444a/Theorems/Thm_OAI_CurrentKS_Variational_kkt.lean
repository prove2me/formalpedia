-- Prove2me | Theorems.Thm_OAI_CurrentKS_Variational_kkt
-- name    : OAI.CurrentKS.Variational.kkt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:56.144679+00:00
-- url     : https://prove2.me/theorems/3f9d6633-fa03-41af-a0d6-b1d821c22c8b
-- title:
--   OAI.CurrentKS.Variational.kkt: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.Variational`, with `open Matrix`, `open CurrentKS.Hermitian Matrix Set`, `open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius`):
--
--   ```lean
--   theorem kkt [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
--       (hηpos : ∀ A ∈ psdCone d, η A ∈ psdCone d) (hηsym : SymmetricMap η)
--       {ε K : ℝ} (hε : 0 < ε)
--       (hS₁ : -K • ((Hermitian.one : H d) : H d) ≤ S) (hS₂ : S ≤ K • ((Hermitian.one : H d) : H d))
--       (z : Point d) (hz : z ∈ feasible S η)
--       (hmin : ∀ w ∈ feasible S η, objective ε z ≤ objective ε w) :
--       ∃ P Q : H d, P ∈ pd d ∧ Q ∈ pd d ∧ P ≤ (Hermitian.one : H d) ∧ Q ≤ (Hermitian.one : H d) ∧
--         _root_.OAI.CurrentKS.Hermitian.realTrace P + _root_.OAI.CurrentKS.Hermitian.realTrace Q = 1 ∧
--         P = sandwich z.2.1 (η Q) + ε • sandwich z.2.1 (Hermitian.one : H d) ∧
--         Q = sandwich z.2.2 (η P) + ε • sandwich z.2.2 (Hermitian.one : H d) ∧
--         residual S η z = 0 ∧
--         sandwich (invH z.2.1) P = η Q + ε • (Hermitian.one : H d) ∧
--         sandwich (invH z.2.2) Q = η P + ε • (Hermitian.one : H d)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.Hermitian.H`, `OAI.CurrentKS.Hermitian.Mat`, `OAI.CurrentKS.Hermitian.invH`, `OAI.CurrentKS.Hermitian.one`, `OAI.CurrentKS.Hermitian.pd`, `OAI.CurrentKS.Hermitian.psdCone`, `OAI.CurrentKS.Hermitian.realTrace`, `OAI.CurrentKS.Hermitian.sandwich`, `OAI.CurrentKS.Variational.Point`, `OAI.CurrentKS.Variational.SymmetricMap`, `OAI.CurrentKS.Variational.feasible`, `OAI.CurrentKS.Variational.objective` and `OAI.CurrentKS.Variational.residual` (definitions bundle `OAIQ241TT002` of this split).
--
--   **Used by.** The proofs of `OAI.CurrentKS.RationalFace.faceCandidates_progress`, `OAI.CurrentKS.State.value_strip_derivatives`, `OAI.CurrentKS.Variational.contDiffAt_value` and `OAI.CurrentKS.Variational.value_derivatives_majorant` of this split import it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ241TT002

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

theorem kkt [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hηpos : ∀ A ∈ psdCone d, η A ∈ psdCone d) (hηsym : SymmetricMap η)
    {ε K : ℝ} (hε : 0 < ε)
    (hS₁ : -K • ((Hermitian.one : H d) : H d) ≤ S) (hS₂ : S ≤ K • ((Hermitian.one : H d) : H d))
    (z : Point d) (hz : z ∈ feasible S η)
    (hmin : ∀ w ∈ feasible S η, objective ε z ≤ objective ε w) :
    ∃ P Q : H d, P ∈ pd d ∧ Q ∈ pd d ∧ P ≤ (Hermitian.one : H d) ∧ Q ≤ (Hermitian.one : H d) ∧
      _root_.OAI.CurrentKS.Hermitian.realTrace P + _root_.OAI.CurrentKS.Hermitian.realTrace Q = 1 ∧
      P = sandwich z.2.1 (η Q) + ε • sandwich z.2.1 (Hermitian.one : H d) ∧
      Q = sandwich z.2.2 (η P) + ε • sandwich z.2.2 (Hermitian.one : H d) ∧
      residual S η z = 0 ∧
      sandwich (invH z.2.1) P = η Q + ε • (Hermitian.one : H d) ∧
      sandwich (invH z.2.2) Q = η P + ε • (Hermitian.one : H d) := by
  sorry

end
end CurrentKS.Variational

end OAI
end
