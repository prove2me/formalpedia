-- Prove2me | Theorems.Thm_OAI_GAD_output_entropy_recursion
-- name    : OAI.GAD.output_entropy_recursion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:27:39.503039+00:00
-- url     : https://prove2.me/theorems/4dc2209a-64fb-4a12-8d7a-43a18d5a7e4c
-- title:
--   Entropy recursion for pure inputs of the generalized amplitude-damping channel
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
--   Let $n\in\mathbb{N}$ and let $\psi\in\mathbb{C}^{\{0,1\}^{n+1}}$ be a unit vector, $\sum_w|\psi_w|^2=1$. Its branches along the first qubit are $\psi_a\in\mathbb{C}^{\{0,1\}^n}$, $\psi_a(i)=\psi(ai)$ for $a\in\{0,1\}$, where $ai$ is the word with first letter $a$ followed by $i$. Put $x=\|\psi_0\|^2$ and $y=\|\psi_1\|^2$, and let the normalized branches be $\hat\psi_a=\psi_a/\|\psi_a\|$ if $\psi_a\neq0$, and $\hat\psi_a=|0\cdots0\rangle$ (the basis vector of the all-zero word) if $\psi_a=0$. Let $p_0(\psi)=\sum_{w:\,w_0=1}|\psi_w|^2$ be the population of $|1\rangle$ at the first qubit (so $p_0(\psi)=y$). Then
--   $$
--   x\,S\big(\Phi_n(|\hat\psi_0\rangle\langle\hat\psi_0|)\big)+y\,S\big(\Phi_n(|\hat\psi_1\rangle\langle\hat\psi_1|)\big)+g\big(v(p_0(\psi))\big)\le S\big(\Phi_{n+1}(|\psi\rangle\langle\psi|)\big).
--   $$
--
--   One checks that $g(v(p))$ is the entropy of the single-qubit output $\sum_rA_r|\phi\rangle\langle\phi|A_r^{*}$ of a pure qubit state $\phi$ with $|1\rangle$-population $p$: this output has trace $1$ and determinant $v(p)$, hence eigenvalues $\tfrac12\big(1\pm\sqrt{1-4v(p)}\big)$. The inequality thus says that, peeling off the first qubit, the output entropy of a pure $(n+1)$-qubit input is at least the single-qubit output entropy at the first site plus the average output entropy of the two normalized conditional $n$-qubit inputs. Iterated over all qubits, together with convexity of $p\mapsto g(v(p))$, it yields a lower bound on the output entropy of every pure input, entangled or not, in terms of its single-site populations.
--
--   **Formalization Note** $\hat\psi_a$ is `normalize (branch ψ a)`, which returns the basis vector of the all-zero word when the branch vanishes; in that case the corresponding weight $x$ or $y$ is $0$. Further, $\|\cdot\|^2$ is `vecMass`, $p_0(\psi)$ is `population ψ 0`, $|\phi\rangle\langle\phi|$ is `pure φ`, $S$ is `entropy` and $h$ is `Real.binEntropy`. The case $n=0$ is included.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/PureRecursion.lean#L261-L306

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

open OAI OAI.GAD
universe u_1 u_2 u_3 u_4
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_2} {κ : Type u_3} {ρ : Type u_4} [Fintype ι] [Fintype κ] [Fintype ρ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ]

theorem OAI.GAD.output_entropy_recursion (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (ψ : Basis (n+1) → ℂ)
    (hψ : vecMass ψ = 1) :
    vecMass (branch ψ 0) * entropy (channel γ ν n (pure (normalize (branch ψ 0)))) +
      vecMass (branch ψ 1) * entropy (channel γ ν n (pure (normalize (branch ψ 1)))) +
      g (v γ ν (population ψ 0)) ≤ entropy (channel γ ν (n+1) (pure ψ)) := by sorry
