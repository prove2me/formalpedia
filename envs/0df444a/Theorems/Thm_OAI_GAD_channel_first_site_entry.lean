-- Prove2me | Theorems.Thm_OAI_GAD_channel_first_site_entry
-- name    : OAI.GAD.channel_first_site_entry
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:26:54.62937+00:00
-- url     : https://prove2.me/theorems/4050a504-1839-4153-ac96-c2027a531d30
-- title:
--   First-qubit block formula for the $(n+1)$-qubit generalized amplitude-damping channel on pure inputs
-- statement:
--   Fix real numbers $\gamma,\nu$ (no range restriction is needed) and let $A_0,A_1,A_2,A_3$ be the single-qubit generalized amplitude-damping Kraus operators, the complex $2\times2$ matrices with rows and columns indexed by $\{0,1\}$
--   $$
--   A_0=\begin{pmatrix}\sqrt{1-\nu}&0\\0&\sqrt{1-\nu}\,\sqrt{1-\gamma}\end{pmatrix},\quad A_1=\begin{pmatrix}0&\sqrt{\gamma(1-\nu)}\\0&0\end{pmatrix},\quad A_2=\begin{pmatrix}\sqrt{\nu}\,\sqrt{1-\gamma}&0\\0&\sqrt{\nu}\end{pmatrix},\quad A_3=\begin{pmatrix}0&0\\\sqrt{\gamma\nu}&0\end{pmatrix}.
--   $$
--   Here $\sqrt{\cdot}$ is the real square root. For a $2\times2$ complex matrix $N$ write $\mathcal{A}(N)=\sum_{r=0}^{3}A_rNA_r^{*}$ for the single-qubit channel. For $n\in\mathbb{N}$, $n$-qubit operators are complex matrices indexed by words $w=(w_0,\dots,w_{n-1})\in\{0,1\}^n$. For a Kraus multi-index $R\in\{0,1,2,3\}^n$ let $K_R=A_{R_0}\otimes\cdots\otimes A_{R_{n-1}}$, that is $(K_R)_{ww'}=\prod_{k=0}^{n-1}(A_{R_k})_{w_kw'_k}$, and let $\Phi_n(P)=\sum_{R\in\{0,1,2,3\}^n}K_R\,P\,K_R^{*}$ be the memoryless $n$-fold channel ($K^{*}$ denotes the conjugate transpose). For a vector $\phi$, $|\phi\rangle\langle\phi|$ is the matrix with entries $\phi_w\overline{\phi_{w'}}$.
--
--   Let $\psi\in\mathbb{C}^{\{0,1\}^{n+1}}$ be any vector (not necessarily normalized). For $b\in\{0,1\}$ and $i\in\{0,1\}^n$ write $bi\in\{0,1\}^{n+1}$ for the word with first letter $b$ followed by $i$, and let $\psi_a\in\mathbb{C}^{\{0,1\}^n}$, $\psi_a(i)=\psi(ai)$, be the two branches of $\psi$ along the first qubit. Let $C_a$ be the $2^n\times4^n$ matrix whose column with index $R\in\{0,1,2,3\}^n$ is the vector $K_R\psi_a$. Then for all $b,c\in\{0,1\}$ and all $i,j\in\{0,1\}^n$,
--   $$
--   \Phi_{n+1}\big(|\psi\rangle\langle\psi|\big)_{bi,\,cj}=\mathcal{A}\big(N^{(ij)}\big)_{bc},\qquad N^{(ij)}_{ad}=\big(C_aC_d^{*}\big)_{ij}=\sum_{R\in\{0,1,2,3\}^n}(K_R\psi_a)_i\,\overline{(K_R\psi_d)_j}\quad(a,d\in\{0,1\}).
--   $$
--
--   In words: in block form with respect to the first qubit, the output on a pure input is obtained by feeding the $2\times2$ array of $n$-qubit cross outputs $C_aC_d^{*}=\sum_RK_R|\psi_a\rangle\langle\psi_d|K_R^{*}$ through the single-qubit channel, which is the concrete form of $\Phi_{n+1}=\mathcal{A}\otimes\Phi_n$ on pure inputs. Combined with the explicit action of $\mathcal{A}$ it expresses $\Phi_{n+1}(|\psi\rangle\langle\psi|)$ as a $2\times2$ block matrix built from the outputs of the two branches, the starting point of the entropy recursion for this channel.
--
--   **Formalization Note** The word $bi$ is `Fin.cons b i`, $\psi_a$ is `branch ψ a`, $C_a$ is `columns (tensorKraus γ ν n) (branch ψ a)`, $\mathcal{A}$ is `applyKraus (kraus γ ν)` and $\Phi_n$ is `channel γ ν n`. Since `Real.sqrt` returns $0$ on negative arguments, the Kraus matrices are defined for all real $\gamma,\nu$, and the identity is purely algebraic.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/PureRecursion.lean#L168-L195

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

theorem OAI.GAD.channel_first_site_entry (γ ν : ℝ) {n : ℕ} (ψ : Basis (n+1) → ℂ)
    (b c : Fin 2) (i j : Basis n) :
    channel γ ν (n+1) (pure ψ) (Fin.cons b i) (Fin.cons c j) =
      applyKraus (kraus γ ν)
        (fun a d ↦ (columns (tensorKraus γ ν n) (branch ψ a) *
          (columns (tensorKraus γ ν n) (branch ψ d)).conjTranspose) i j) b c := by sorry
