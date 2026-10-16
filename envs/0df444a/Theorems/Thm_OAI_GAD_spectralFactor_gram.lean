-- Prove2me | Theorems.Thm_OAI_GAD_spectralFactor_gram
-- name    : OAI.GAD.spectralFactor_gram
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:28:58.168467+00:00
-- url     : https://prove2.me/theorems/215f4d7a-18da-4915-8d2c-8940eccc25c1
-- title:
--   The spectral square-root factor $F$ of a positive semidefinite matrix $A$ satisfies $FF^*=A$
-- statement:
--   Let $\iota$ be a finite index set and let $A\in\mathbb{C}^{\iota\times\iota}$ be positive semidefinite. Write its spectral decomposition with eigenvalues $\lambda_k\ge0$ and unitary eigenvector matrix $U$ (column $k$ of $U$ is a unit eigenvector for $\lambda_k$, $k\in\iota$). The spectral factor of $A$ is the matrix $F\in\mathbb{C}^{\iota\times\iota}$ with entries $F_{ik}=\sqrt{\lambda_k}\,U_{ik}$, i.e. $F=U\,\mathrm{diag}(\sqrt{\lambda})$. Then its Gram matrix recovers $A$:
--   $$
--   FF^{*}=A ,
--   $$
--   where $F^{*}$ denotes the conjugate transpose.
--
--   The factor $F$ is an explicit matrix with $A=FF^{*}$ whose columns are the scaled eigenvectors $\sqrt{\lambda_k}\,u_k$. In particular every density matrix is the Gram matrix of a factor of Frobenius norm $\operatorname{Tr}(FF^{*})=1$, which allows statements about states to be transferred to the Euclidean geometry of their factors (Naimark dilations, entropy continuity estimates, comparison of states through their factors).
--
--   **Formalization Note** $F$ is `spectralFactor hA`, built from Mathlib's `eigenvalues` and `eigenvectorUnitary` of the Hermitian matrix underlying `hA`, and $FF^{*}$ is `gram F`. The type `α` in the variable context is unused.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/StateEntropy.lean#L104-L119

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
variable {ι : Type u_3} {α : Type u_4} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

theorem OAI.GAD.spectralFactor_gram {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    gram (spectralFactor hA) = A := by sorry
