-- Prove2me | Theorems.Thm_OAI_GAD_entropy_reindex
-- name    : OAI.GAD.entropy_reindex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:25:20.648318+00:00
-- url     : https://prove2.me/theorems/bdf6b60d-8ba2-4dc2-8082-0877af6ae494
-- title:
--   Matrix entropy is invariant under relabeling of indices
-- statement:
--   Let $\iota$ and $\kappa$ be finite index sets, let $e:\iota\to\kappa$ be a bijection, and let $A\in\mathbb{C}^{\iota\times\iota}$ be Hermitian. Let $A^e\in\mathbb{C}^{\kappa\times\kappa}$ be the matrix obtained by relabeling rows and columns along $e$, namely $(A^e)_{kl}=A_{e^{-1}(k)\,e^{-1}(l)}$. With the matrix entropy $S(B)=\operatorname{Re}\operatorname{Tr}\eta(B)$, defined through the functional calculus with $\eta(x)=-x\log x$,
--
--   $$
--   S(A^e)=S(A).
--   $$
--
--   Relabeling basis vectors is a permutation similarity and does not change the spectrum, hence does not change the entropy. The identity lets one move between different index sets for the same space, for instance between labels of $(n+1)$-qubit basis states and pairs consisting of a one-qubit label and an $n$-qubit label.
--
--   **Formalization Note** $A^e$ is `Matrix.reindex e e A`, where `e` is an equivalence `ι ≃ κ`. Only Hermiticity of $A$ is assumed; for negative eigenvalues the entropy function uses Lean's convention $\log x=\log|x|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/TensorEntropy.lean#L65-L78

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy

open OAI OAI.GAD
universe u_1 u_2 u_3 u_4
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder
open scoped BigOperators
open Set Filter Topology
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open Matrix
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem OAI.GAD.entropy_reindex (e : ι ≃ κ) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    entropy (Matrix.reindex e e A) = entropy A := by sorry
