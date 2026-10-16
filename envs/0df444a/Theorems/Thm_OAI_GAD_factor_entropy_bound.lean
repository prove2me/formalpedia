-- Prove2me | Theorems.Thm_OAI_GAD_factor_entropy_bound
-- name    : OAI.GAD.factor_entropy_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:31:58.66195+00:00
-- url     : https://prove2.me/theorems/4affcd7c-88a4-4b94-bb15-c631b66e26d7
-- title:
--   Entropy comparison of Gram matrices with close unit-norm factors
-- statement:
--   Let $\iota,\kappa$ be finite index sets with $\iota$ nonempty, and let $d=|\iota|$. For $Z\in\mathbb{C}^{\iota\times\kappa}$ let $Z^{*}$ be its conjugate transpose and $\|Z\|_F^2=\operatorname{Tr}(ZZ^{*})=\sum_{i,k}|Z_{ik}|^2$ its squared Frobenius norm. For a positive semidefinite matrix $P$ with eigenvalues $\lambda_k$ let $S(P)=-\sum_k\lambda_k\log\lambda_k$ (natural logarithm, $0\log0=0$).
--
--   Let $X,Y\in\mathbb{C}^{\iota\times\kappa}$ satisfy $\|X\|_F=\|Y\|_F=1$, so that $XX^{*}$ and $YY^{*}$ are density matrices on $\mathbb{C}^\iota$, and let $\varepsilon>0$. Then
--   $$
--   S(XX^{*})-S(YY^{*})\le\Big(\frac{\|X-Y\|_F^2}{4\varepsilon}+\varepsilon\Big)\log d+\Big(1+\frac{\|X-Y\|_F^2}{4\varepsilon}+\varepsilon\Big)\log 2 .
--   $$
--
--   Every density matrix is the Gram matrix of a unit-norm factor, so this bounds entropy differences by the distance between factors. The free parameter $\varepsilon$ balances the two error contributions: choosing $\varepsilon$ of order $\|X-Y\|_F$ makes the coefficient of $\log d$ of order $\|X-Y\|_F$, while an additive term of about $\log2$ remains. In the development it enters the converse estimate that relates decoding success to the Holevo quantity.
--
--   **Formalization Note** $\|Z\|_F^2$ is `mass Z`, $ZZ^{*}$ is `gram Z`, $S$ is `entropy` and $d$ is `Fintype.card ι`. The bound holds for every $\varepsilon>0$; no smallness of $\|X-Y\|_F$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/EntropyContinuity.lean#L198-L268

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

open OAI OAI.GAD
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_4} {κ : Type u_5} [Fintype ι] [Fintype κ]
variable [DecidableEq ι]

theorem OAI.GAD.factor_entropy_bound [Nonempty ι] (X Y : Matrix ι κ ℂ)
    (hX : mass X=1) (hY : mass Y=1) {ε : ℝ} (hε : 0 < ε) :
    entropy (gram X)-entropy (gram Y) ≤
      (mass (X-Y)/(4*ε)+ε)*Real.log (Fintype.card ι)+
        (1+mass (X-Y)/(4*ε)+ε)*Real.log 2 := by sorry
