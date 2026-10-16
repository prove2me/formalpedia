-- Prove2me | Theorems.Thm_OAI_GAD_phase_rate_achievable
-- name    : OAI.GAD.phase_rate_achievable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:03:31.259036+00:00
-- url     : https://prove2.me/theorems/9fce2e01-ac3a-4a59-942d-cfaa15601817
-- title:
--   Every rate below the phase-ensemble Holevo quantity is achievable for generalized amplitude damping
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
--   A real number $R$ (a rate in bits per channel use) is *achievable* if there are $n$-use codes $C_n$, one for every $n\ge0$, with $M_n$ messages, such that $\bar e(C_n)\to0$ as $n\to\infty$ and, for every $\varepsilon>0$, $R-\varepsilon\le\frac{\log_2M_n}{n}$ for all sufficiently large $n$. No entanglement assistance or feedback is involved, and encodings and the collective decoding measurement are unrestricted.
--
--   All logarithms are natural. Let $h(t)=-t\log t-(1-t)\log(1-t)$ be the binary entropy, and put
--
--   $$
--   g(u)=h\Bigl(\frac{1+\sqrt{1-4u}}{2}\Bigr),\qquad v(p)=\gamma\nu(1-\nu)+\gamma(1-\gamma)(p-\nu)^2,\qquad \chi(p)=h\bigl((1-\gamma)p+\gamma\nu\bigr)-g\bigl(v(p)\bigr).
--   $$
--
--   **Theorem.** Let $\gamma,\nu,p\in[0,1]$ and let $r$ be a real number with $0\le r<\chi(p)$. Then $r/\log2$ is an achievable rate: there are $n$-use codes $C_n$ with $M_n$ messages such that
--
--   $$
--   \lim_{n\to\infty}\bar e(C_n)=0\qquad\text{and}\qquad\forall\varepsilon>0\ \exists N\ \forall n\ge N:\quad\frac{r}{\log2}-\varepsilon\le\frac{\log_2M_n}{n}.
--   $$
--
--   Here $r$ is a rate in nats and $r/\log2$ the same rate in bits. The number $\chi(p)$ is the Holevo quantity, in nats, of the equiprobable ensemble of the two phase signals $\bigl(\sqrt{1-p},\pm\sqrt p\bigr)$. Letting $r$ increase to $\chi(p)$ shows that the operational classical capacity of the channel is at least $\chi(p)/\log2$ for every $p\in[0,1]$, in particular for a maximizer of $\chi$; together with a matching converse this identifies the capacity.
--
--   **Formalization Note** $\chi(p)$ is `objective γ ν p`, achievability is the predicate `Achievable γ ν R`, and $\log_2M_n$ is written as `Real.log M / Real.log 2`. For $n=0$ Lean's division by zero gives the value $0$, which does not matter since the rate condition is required only eventually.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/CapacityAchievability.lean#L10-L42

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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_CodingAsymptotics

open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter

theorem OAI.GAD.phase_rate_achievable (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1)
    {r : ℝ} (hr : 0 ≤ r) (hrχ : r < objective γ ν p) :
    Achievable γ ν (r/Real.log 2) := by sorry
