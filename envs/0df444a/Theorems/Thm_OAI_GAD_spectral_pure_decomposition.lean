-- Prove2me | Theorems.Thm_OAI_GAD_spectral_pure_decomposition
-- name    : OAI.GAD.spectral_pure_decomposition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:28:16.79433+00:00
-- url     : https://prove2.me/theorems/c8e40a89-91d1-48eb-b922-2fc5b36dbb2a
-- title:
--   Spectral decomposition of a Hermitian matrix into rank-one matrices
-- statement:
--   Let $\iota$ be a finite index set and let $P\in\mathbb{C}^{\iota\times\iota}$ be a Hermitian matrix. By the spectral theorem there are real eigenvalues $\lambda_a$ and a unitary matrix $U\in\mathbb{C}^{\iota\times\iota}$, indexed by $a\in\iota$, such that the columns $u_a=(U_{ia})_{i\in\iota}$ form an orthonormal basis of eigenvectors, $Pu_a=\lambda_au_a$. For a vector $u\in\mathbb{C}^\iota$ write $|u\rangle\langle u|$ for the matrix with entries $u_i\overline{u_j}$. Then
--   $$
--   P=\sum_{a\in\iota}\lambda_a\,|u_a\rangle\langle u_a| .
--   $$
--
--   This writes a Hermitian matrix, in particular a density matrix, as a real linear combination of rank-one pure-state matrices taken from a fixed orthonormal eigenbasis. It is the form of the spectral theorem used to build square-root factors $F$ with $FF^{*}=P$ for positive semidefinite $P$, and to pass between mixed states and ensembles of pure states.
--
--   **Formalization Note** The eigenvalues and eigenvector matrix are Mathlib's `hP.eigenvalues` and `hP.eigenvectorUnitary`, both indexed by $\iota$ itself (eigenvalues listed with multiplicity), and $|u\rangle\langle u|$ is `pure u`. The type `α` that appears in the variable context of the statement plays no role.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/StateEntropy.lean#L24-L36

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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PureRecursion
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_StateEntropy

open OAI OAI.GAD
universe u_1 u_2 u_3 u_4
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α]

theorem OAI.GAD.spectral_pure_decomposition {P : Matrix ι ι ℂ} (hP : P.IsHermitian) :
    P = ∑ a, hP.eigenvalues a • pure (fun i ↦ hP.eigenvectorUnitary i a) := by sorry
