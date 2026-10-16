-- Prove2me | Theorems.Thm_OAI_GAD_exists_orthogonal_factors
-- name    : OAI.GAD.exists_orthogonal_factors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:36:20.651663+00:00
-- url     : https://prove2.me/theorems/3e87fe1e-4ae9-4995-824c-30fc911a28a0
-- title:
--   Approximately orthogonal factors for well-decoded states in a Naimark dilation
-- statement:
--   Let $\iota$ and $\mu$ be finite index sets ($\mu$ indexes messages). Let $(A_m)_{m\in\mu}$ be density matrices on $\mathbb{C}^\iota$ (positive semidefinite with trace $1$) and let $(D_m)_{m\in\mu}$ be a POVM on $\mathbb{C}^\iota$: positive semidefinite matrices with $\sum_mD_m=I$. We use the following notation ($Z^{*}$ is the conjugate transpose).
--
--   1. For a positive semidefinite $M\in\mathbb{C}^{\iota\times\iota}$ with eigenvalues $\lambda_k$ and unitary eigenvector matrix $U$, its spectral factor is $F(M)\in\mathbb{C}^{\iota\times\iota}$, $F(M)_{ik}=\sqrt{\lambda_k}\,U_{ik}$; it satisfies $F(M)F(M)^{*}=M$.
--   2. The Naimark matrix $W\in\mathbb{C}^{(\iota\times\mu)\times\iota}$ has entries $W_{(i,m),j}=\overline{F(D_m)_{ji}}$, i.e. its $m$-th block of rows is $F(D_m)^{*}$; because $\sum_mD_m=I$ it is an isometry, $W^{*}W=I$.
--   3. The block projection $\Pi_m$ on $\mathbb{C}^{\iota\times\mu}$ is the diagonal matrix with entry $1$ at the indices $(i,m)$, $i\in\iota$, and $0$ elsewhere.
--   4. $\|Z\|_F^2=\operatorname{Tr}(ZZ^{*})$ is the squared Frobenius norm.
--
--   Then there are matrices $Y_m\in\mathbb{C}^{(\iota\times\mu)\times\iota}$, $m\in\mu$, such that for every $m$ we have $\|Y_m\|_F=1$, $\Pi_mY_m=Y_m$, and
--   $$
--   \big\|W\,F(A_m)-Y_m\big\|_F^2\le2\Big(1-\operatorname{Re}\operatorname{Tr}(D_mA_m)\Big).
--   $$
--
--   Here $WF(A_m)$ is a unit-norm factor of the dilated state $WA_mW^{*}$, and $\operatorname{Tr}(D_mA_m)$ is the probability that the measurement $(D_m)$ correctly decodes the message $m$ when $A_m$ is sent. The factors $Y_m$ live on mutually orthogonal blocks, so they describe perfectly distinguishable states; the lemma moves each dilated factor onto its own block at a squared cost of twice its decoding error. This is how decoding success is converted into a lower bound on the Holevo quantity.
--
--   **Formalization Note** $F(M)$ is `spectralFactor`, $W$ is `naimark D hD`, $\Pi_m$ is `blockProjection m`, and $\|Z\|_F^2$ is `mass Z`. The isometry property of $W$ is used in the proof and is not part of the statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/Naimark.lean#L55-L71

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
variable {ι : Type u_1} {μ : Type u_2} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

theorem OAI.GAD.exists_orthogonal_factors (A D : μ → Matrix ι ι ℂ)
    (hA : ∀ m, IsState (A m)) (hD : ∀ m, (D m).PosSemidef) (hDs : ∑ m, D m=1) :
    ∃ Y : μ → Matrix (ι × μ) ι ℂ,
      (∀ m, mass (Y m)=1) ∧ (∀ m, blockProjection (ι := ι) m*Y m=Y m) ∧
      (∀ m, mass (naimark D hD*spectralFactor (hA m).1-Y m) ≤ 2*(1-(D m*A m).trace.re)) := by sorry
