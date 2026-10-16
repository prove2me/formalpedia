-- Prove2me | Theorems.Thm_OAI_GAD_orthogonal_factor_entropy
-- name    : OAI.GAD.orthogonal_factor_entropy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:36:55.432517+00:00
-- url     : https://prove2.me/theorems/a69bde3a-c524-424e-84e8-13b57ef69934
-- title:
--   Entropy of a weighted sum of states supported on orthogonal blocks
-- statement:
--   Let $\iota,\kappa,\mu$ be finite index sets. For $m\in\mu$ let $\Pi_m$ be the block projection on $\mathbb{C}^{\iota\times\mu}$, the diagonal matrix with entry $1$ at the indices $(i,m)$, $i\in\iota$, and $0$ elsewhere. For a complex matrix $Z$ let $Z^{*}$ be its conjugate transpose and $\|Z\|_F^2=\operatorname{Tr}(ZZ^{*})$. For a Hermitian matrix $H$ with eigenvalues $\lambda_k$ (with multiplicity) put $S(H)=\sum_k\eta(\lambda_k)$, where $\eta(0)=0$ and $\eta(x)=-x\log|x|$ for $x\ne0$ (natural logarithm); on positive semidefinite matrices this is $-\operatorname{Tr}H\log H$, the von Neumann entropy.
--
--   Let $w=(w_m)_{m\in\mu}$ be arbitrary real numbers and let $Y_m\in\mathbb{C}^{(\iota\times\mu)\times\kappa}$ satisfy $\|Y_m\|_F=1$ and $\Pi_mY_m=Y_m$ for every $m$ (all rows of $Y_m$ outside block $m$ vanish). Then
--   $$
--   S\Big(\sum_{m\in\mu}w_m\,Y_mY_m^{*}\Big)=\sum_{m\in\mu}\Big(w_m\,S\big(Y_mY_m^{*}\big)+\eta(w_m)\Big).
--   $$
--
--   The states $\rho_m=Y_mY_m^{*}$ are supported on mutually orthogonal subspaces. For a probability vector $w$ the identity is the familiar formula $S\big(\sum_mw_m\rho_m\big)=\sum_mw_mS(\rho_m)+H(w)$, where $H(w)=\sum_m\eta(w_m)$ is the Shannon entropy: an ensemble of perfectly distinguishable states has Holevo quantity exactly $H(w)$. This exact computation is the reference point against which the decoding-based estimates are compared.
--
--   **Formalization Note** $\Pi_m$ is `blockProjection m`, $Y_mY_m^{*}$ is `gram (Y m)`, $\|Y_m\|_F^2$ is `mass (Y m)`, $\eta$ is `Real.negMulLog` and $S$ is `entropy`. No sign or normalization condition on $w$ is assumed: with Mathlib's convention $\log x=\log|x|$ the identity holds for all real weights.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/Naimark.lean#L119-L140

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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EntropyContinuity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_BlockFactors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Naimark

open OAI OAI.GAD
universe u_1 u_2 u_3 u_4 u_5
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_3} {κ : Type u_4} {μ : Type u_5} [Fintype ι] [Fintype κ] [Fintype μ]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]

theorem OAI.GAD.orthogonal_factor_entropy (w : μ → ℝ) (Y : μ → Matrix (ι × μ) κ ℂ)
    (hY : ∀ m, mass (Y m)=1) (hPY : ∀ m, blockProjection (ι := ι) m*Y m=Y m) :
    entropy (∑ m, w m • gram (Y m))=
      ∑ m, (w m*entropy (gram (Y m))+Real.negMulLog (w m)) := by sorry
