-- Prove2me | Theorems.Thm_OAI_GAD_cq_decoding_entropy_bound
-- name    : OAI.GAD.cq_decoding_entropy_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:37:52.526346+00:00
-- url     : https://prove2.me/theorems/1244e78e-812e-43cc-ba47-b72cb325a1f1
-- title:
--   Decoding success forces a large Holevo quantity: a one-shot converse bound
-- statement:
--   Let $\iota$ and $\mu$ be nonempty finite index sets, and let $M=|\mu|$ be the number of messages. Let $(A_m)_{m\in\mu}$ be density matrices on $\mathbb{C}^\iota$ (positive semidefinite with trace $1$), and let $(D_m)_{m\in\mu}$ be a decoding POVM: positive semidefinite matrices on $\mathbb{C}^\iota$ with $\sum_mD_m=I$. For a density matrix $\rho$ with eigenvalues $\lambda_k$ let $S(\rho)=-\sum_k\lambda_k\log\lambda_k$ be its von Neumann entropy (natural logarithm, $0\log0=0$). The average success probability is
--   $$\bar s=\frac1M\sum_{m\in\mu}\operatorname{Re}\operatorname{Tr}(D_mA_m),$$
--   and for $\varepsilon>0$, $\delta\in\mathbb{R}$ and $N\in\mathbb{N}$ put
--   $$\varphi_\varepsilon(\delta,N)=\Big(\frac{\delta}{4\varepsilon}+\varepsilon\Big)\log N+\Big(1+\frac{\delta}{4\varepsilon}+\varepsilon\Big)\log2 .$$
--   Then for every $\varepsilon>0$,
--   $$
--   \log M\le S\Big(\frac1M\sum_{m\in\mu}A_m\Big)-\frac1M\sum_{m\in\mu}S(A_m)+2\,\varphi_\varepsilon\big(2(1-\bar s),\,|\iota|\,M\big).
--   $$
--
--   The first two terms on the right form the Holevo quantity of the equiprobable ensemble $\{A_m\}$. The bound says that if the $M$ states can be decoded with small average error $1-\bar s$, then this Holevo quantity is at least $\log M$, up to an error controlled by $1-\bar s$, $\varepsilon$ and $\log(|\iota|M)$. For codes over $n$ channel uses, where $\log|\iota|$ and $\log M$ grow linearly in $n$, this is the converse inequality that bounds achievable communication rates by the Holevo quantity.
--
--   **Formalization Note** The weights $1/M$ are `uniformWeight μ m`, $\varphi_\varepsilon(\delta,N)$ is `factorError ε δ N`, the dimension $|\iota|\,M$ enters as `Fintype.card (ι × μ)`, and the success term is the real part of the complex trace `(D m * A m).trace`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/HolevoInformation.lean#L91-L132

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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_HolevoInformation

open OAI OAI.GAD
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_5} {μ : Type u_6} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]
  [Nonempty ι] [Nonempty μ]

theorem OAI.GAD.cq_decoding_entropy_bound (A D : μ → Matrix ι ι ℂ)
    (hA : ∀ m, IsState (A m)) (hD : ∀ m, (D m).PosSemidef) (hDs : ∑ m, D m=1)
    {ε : ℝ} (hε : 0 < ε) :
    Real.log (Fintype.card μ) ≤
      entropy (∑ m, uniformWeight μ m • A m)-(∑ m, uniformWeight μ m*entropy (A m))+
      2*factorError ε (2*(1-∑ m, uniformWeight μ m*(D m*A m).trace.re)) (Fintype.card (ι × μ)) := by sorry
