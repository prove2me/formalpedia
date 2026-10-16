-- Prove2me | Theorems.Thm_OAI_GAD_entropy_unitary_conj
-- name    : OAI.GAD.entropy_unitary_conj
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:15:06.964884+00:00
-- url     : https://prove2.me/theorems/776c565b-9b1d-41e0-beb4-74a5254b38b4
-- title:
--   Matrix entropy is invariant under unitary conjugation
-- statement:
--   Let $\iota$ be a finite index set, let $U\in\mathbb{C}^{\iota\times\iota}$ be unitary, and let $A\in\mathbb{C}^{\iota\times\iota}$ be Hermitian. For a Hermitian matrix $B=W\operatorname{diag}(\mu)W^*$ ($W$ unitary, $\mu$ real) let $\eta(B)=W\operatorname{diag}(\eta(\mu_j))W^*$ be defined by the functional calculus, where $\eta(x)=-x\log x$, and let $S(B)=\operatorname{Tr}\eta(B)=\sum_j\eta(\mu_j)$ be the (unnormalized) von Neumann entropy. Then
--
--   $$
--   S(UAU^*)=S(A).
--   $$
--
--   Entropy depends only on the spectrum, so it is unchanged by a unitary change of orthonormal basis. This invariance is used constantly: to pass to an eigenbasis, to identify block matrices that differ by a permutation of blocks, and to compare entropies of matrices written in different bases.
--
--   **Formalization Note** The conjugation $A\mapsto UAU^*$ is `Unitary.conjStarAlgAut ℂ _ U A`, and `entropy B` is the real part of the trace of `cfc Real.negMulLog B`. Only Hermiticity of $A$ is assumed; for negative eigenvalues the entropy function uses Lean's convention $\log x=\log|x|$, which plays no role in the identity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/SpectralEntropy.lean#L94-L110

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity

open OAI OAI.GAD
universe u_1
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

theorem OAI.GAD.entropy_unitary_conj (U : Matrix.unitaryGroup ι ℂ)
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    entropy (Unitary.conjStarAlgAut ℂ _ U A) = entropy A := by sorry
