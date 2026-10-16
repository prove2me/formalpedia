-- Prove2me | Theorems.Thm_OAI_GAD_exists_phase_code
-- name    : OAI.GAD.exists_phase_code
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:01:00.385832+00:00
-- url     : https://prove2.me/theorems/cbe81d71-d85a-4f53-a69f-443bec5a2f1d
-- title:
--   Finite-length coding bound for generalized amplitude damping from phase signals
-- statement:
--   Fix noise parameters $\gamma,\nu\in[0,1]$. The single-qubit generalized amplitude-damping channel acts on $2\times2$ complex matrices by $\mathcal N(\rho)=\sum_{k=0}^{3}K_k\rho K_k^{*}$, with Kraus operators
--
--   $$
--   K_0=\sqrt{1-\nu}\begin{pmatrix}1&0\\0&\sqrt{1-\gamma}\end{pmatrix},\quad K_1=\begin{pmatrix}0&\sqrt{\gamma(1-\nu)}\\0&0\end{pmatrix},\quad K_2=\sqrt{\nu}\begin{pmatrix}\sqrt{1-\gamma}&0\\0&1\end{pmatrix},\quad K_3=\begin{pmatrix}0&0\\\sqrt{\gamma\nu}&0\end{pmatrix}.
--   $$
--
--   Its memoryless $n$-fold extension acts on $2^n\times2^n$ matrices, with rows and columns indexed by bit strings in $\{0,1\}^n$, by $\mathcal N^{\otimes n}(\rho)=\sum_{\mathbf k\in\{0,1,2,3\}^n}K_{\mathbf k}\rho K_{\mathbf k}^{*}$, where $K_{\mathbf k}=K_{k_1}\otimes\cdots\otimes K_{k_n}$. An *$n$-use code* $C$ consists of a number $M\ge1$ of messages, encoding states $\rho_1,\dots,\rho_M$ (positive semidefinite $2^n\times2^n$ matrices of trace one, with no product or purity restriction) and a decoding POVM $D_1,\dots,D_M$ ($D_m\succeq0$ for all $m$ and $\sum_{m}D_m=I$). Its *average error probability* is
--
--   $$
--   \bar e(C)=1-\frac1M\sum_{m=1}^{M}\operatorname{Re}\operatorname{tr}\bigl(D_m\,\mathcal N^{\otimes n}(\rho_m)\bigr).
--   $$
--
--   For $p\in[0,1]$ and a sign bit $s\in\{0,1\}$, the *phase signal* is the unit vector $\psi_s=\bigl(\sqrt{1-p},\,(-1)^s\sqrt p\bigr)\in\mathbb{C}^2$ and $\omega_s=\mathcal N(\psi_s\psi_s^{*})$ is its channel output. All logarithms are natural. For a probability vector $q$ on a finite set write $H(q)=-\sum_iq_i\log q_i$ for its Shannon entropy and $V(q)=\sum_iq_i\bigl(-\log q_i-H(q)\bigr)^2$ for the variance of its surprisal. Let $h(t)=-t\log t-(1-t)\log(1-t)$ be the binary entropy and put
--
--   $$
--   g(u)=h\Bigl(\frac{1+\sqrt{1-4u}}{2}\Bigr),\quad v(p)=\gamma\nu(1-\nu)+\gamma(1-\gamma)(p-\nu)^2,\quad t(p)=(1-\gamma)p+\gamma\nu,\quad \chi(p)=h\bigl(t(p)\bigr)-g\bigl(v(p)\bigr),
--   $$
--
--   and let $\bar q=\bigl(1-t(p),\,t(p)\bigr)$.
--
--   **Theorem.** Let $p\in[0,1]$. Suppose that $q=(q_0,q_1)$ is a probability vector and $U_0,U_1$ are $2\times2$ unitary matrices such that $\omega_s=U_s\operatorname{diag}(q_0,q_1)U_s^{*}$ for $s=0,1$ (both phase outputs have the eigenvalues $q_0,q_1$), and that $H(q)=g(v(p))$. Then for every $\delta>0$, every integer $n\ge1$ and every integer $M\ge1$ there is an $n$-use code $C$ with exactly $M$ messages such that
--
--   $$
--   \bar e(C)\;\le\;\frac{9V(\bar q)+8V(q)}{n\delta^{2}}+4M\,e^{-n(\chi(p)-2\delta)} .
--   $$
--
--   This is an explicit finite-blocklength achievability bound. With $M\approx e^{nr}$ and $r<\chi(p)-2\delta$ the second term decays exponentially in $n$ and the first like $1/n$, which yields codes of rate $\chi(p)/\log2$ bits per channel use. The number $\chi(p)$ is the Holevo quantity, in nats, of the equiprobable ensemble $\{\psi_0,\psi_1\}$: $h(t(p))$ is the entropy of the average output and $g(v(p))$ the entropy of each $\omega_s$. The spectral data $q,U_0,U_1$ always exist; they appear as hypotheses so that the bound can be stated in terms of $V(q)$.
--
--   **Formalization Note** $H$, $V$ and $\bar q$ are `classicalEntropy`, `logVariance` and `meanPhaseWeights γ ν p`; $\omega_s$ is `phaseOutput γ ν p s`, and `spectralMatrix (U s) q` is $U_s\operatorname{diag}(q)U_s^{*}$. Lean's convention $\log0=0$ plays no role in $V$, since every term carries the factor $q_i$. The number of messages is the field `C.messages` of the structure `Code n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/PhaseCoding.lean#L92-L166

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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EnsembleBounds
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseStates
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseProducts
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_CapacityConverse
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TypicalSets
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TypicalProjectors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialDecoder
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseCoding

open OAI OAI.GAD
universe u_1
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

theorem OAI.GAD.exists_phase_code (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1)
    (q : Fin 2 → ℝ) (U : Fin 2 → Matrix.unitaryGroup (Fin 2) ℂ)
    (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i=1)
    (hphase : ∀ s, phaseOutput γ ν p s=spectralMatrix (U s) q)
    (hent : classicalEntropy q=g (v γ ν p))
    {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n) (M : ℕ) (hM : 0 < M) :
    ∃ C : Code n, C.messages=M ∧ averageError γ ν C ≤
      (9*logVariance (meanPhaseWeights γ ν p)+8*logVariance q)/((n:ℝ)*δ^2)+
        4*(M:ℝ)*Real.exp (-(n:ℝ)*(objective γ ν p-2*δ)) := by sorry
