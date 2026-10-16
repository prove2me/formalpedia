-- Prove2me | Theorems.Thm_OAI_GAD_pure_output_entropy_bound
-- name    : OAI.GAD.pure_output_entropy_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:38:28.29403+00:00
-- url     : https://prove2.me/theorems/f04595e4-6fc0-48ee-b367-83d95da92520
-- title:
--   Population-dependent output-entropy lower bound for pure inputs to the $n$-fold generalized amplitude-damping channel
-- statement:
--   Let $\gamma,\nu\in[0,1]$. The single-qubit generalized amplitude-damping channel has the Kraus operators (complex $2\times2$ matrices with rows and columns indexed by $\{0,1\}$)
--   $$
--   A_0=\begin{pmatrix}\sqrt{1-\nu}&0\\0&\sqrt{1-\nu}\,\sqrt{1-\gamma}\end{pmatrix},\quad A_1=\begin{pmatrix}0&\sqrt{\gamma(1-\nu)}\\0&0\end{pmatrix},\quad A_2=\begin{pmatrix}\sqrt{\nu}\,\sqrt{1-\gamma}&0\\0&\sqrt{\nu}\end{pmatrix},\quad A_3=\begin{pmatrix}0&0\\\sqrt{\gamma\nu}&0\end{pmatrix}.
--   $$
--   They satisfy $\sum_rA_r^{*}A_r=I$; $A_1$ moves population from $|1\rangle$ to $|0\rangle$, $A_3$ from $|0\rangle$ to $|1\rangle$, and the diagonal state with $|1\rangle$-population $\nu$ is fixed. For $n\in\mathbb{N}$, $n$-qubit operators are complex matrices indexed by words $w=(w_0,\dots,w_{n-1})\in\{0,1\}^n$. For a Kraus multi-index $R\in\{0,1,2,3\}^n$ let $K_R=A_{R_0}\otimes\cdots\otimes A_{R_{n-1}}$, that is $(K_R)_{ww'}=\prod_{k=0}^{n-1}(A_{R_k})_{w_kw'_k}$, and let $\Phi_n(P)=\sum_{R\in\{0,1,2,3\}^n}K_R\,P\,K_R^{*}$ be the memoryless $n$-fold channel ($K^{*}$ denotes the conjugate transpose). For a vector $\phi$, $|\phi\rangle\langle\phi|$ is the matrix with entries $\phi_w\overline{\phi_{w'}}$.
--
--   For a positive semidefinite matrix $P$ with eigenvalues $\lambda_k$ (with multiplicity) let $S(P)=-\sum_k\lambda_k\log\lambda_k$ (natural logarithm, $0\log0=0$); for $\operatorname{Tr}P=1$ this is the von Neumann entropy. Let $h(x)=-x\log x-(1-x)\log(1-x)$ be the binary entropy and put
--   $$
--   g(u)=h\Big(\frac{1+\sqrt{1-4u}}{2}\Big),\qquad v(p)=\gamma\nu(1-\nu)+\gamma(1-\gamma)(p-\nu)^2 .
--   $$
--
--   Let $n\in\mathbb{N}$ and let $\psi\in\mathbb{C}^{\{0,1\}^n}$ be a unit vector, $\sum_w|\psi_w|^2=1$. For each site $j\in\{0,\dots,n-1\}$ let
--   $$p_j(\psi)=\sum_{w\in\{0,1\}^n:\ w_j=1}|\psi_w|^2$$
--   be the probability of finding qubit $j$ in the state $|1\rangle$. Then
--   $$
--   \sum_{j=0}^{n-1}g\big(v(p_j(\psi))\big)\le S\big(\Phi_n(|\psi\rangle\langle\psi|)\big).
--   $$
--
--   One checks that $g(v(p))$ is the entropy of the single-qubit output $\sum_rA_r|\phi\rangle\langle\phi|A_r^{*}$ of a pure qubit state $\phi$ with $|1\rangle$-population $p$ (that output has trace $1$ and determinant $v(p)$). Hence the output entropy of every pure $n$-qubit input, entangled or not, is at least the total output entropy of a product of pure qubit states with the same single-site populations. This is the pure-input case of the population-dependent output-entropy bound that underlies the additivity of the Holevo quantity of the $n$-fold channel.
--
--   **Formalization Note** $p_j(\psi)$ is `population ψ j`, the normalization is `vecMass ψ = 1`, $|\psi\rangle\langle\psi|$ is `pure ψ`, $S$ is `entropy` and $h$ is `Real.binEntropy`. For $n=0$ the sum is empty and the statement reduces to nonnegativity of the entropy of the output state.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/OutputEntropy.lean#L14-L56

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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputEntropy

open OAI OAI.GAD
universe u_1 u_2 u_3
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

theorem OAI.GAD.pure_output_entropy_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) (ψ : Basis n → ℂ)
    (hψ : vecMass ψ = 1) :
    ∑ j, g (v γ ν (population ψ j)) ≤ entropy (channel γ ν n (pure ψ)) := by sorry
