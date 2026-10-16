-- Prove2me | Theorems.Thm_OAI_GAD_achievable_upper
-- name    : OAI.GAD.achievable_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:44:46.973681+00:00
-- url     : https://prove2.me/theorems/f6488edd-26b8-4915-9fa2-71fa61a71fbf
-- title:
--   Weak converse: achievable rates of the generalized amplitude-damping channel are at most the single-letter Holevo bound
-- statement:
--   Fix noise parameters $\gamma,\nu\in[0,1]$. The generalized amplitude-damping (GAD) channel $\mathcal N_{\gamma,\nu}$ acts on a qubit $\mathbb{C}^2$, with computational basis $|0\rangle,|1\rangle$, through the four Kraus operators
--
--   $$
--   K_0=\sqrt{1-\nu}\begin{pmatrix}1&0\\0&\sqrt{1-\gamma}\end{pmatrix},\quad
--   K_1=\sqrt{\gamma(1-\nu)}\begin{pmatrix}0&1\\0&0\end{pmatrix},\quad
--   K_2=\sqrt{\nu}\begin{pmatrix}\sqrt{1-\gamma}&0\\0&1\end{pmatrix},\quad
--   K_3=\sqrt{\gamma\nu}\begin{pmatrix}0&0\\1&0\end{pmatrix}.
--   $$
--
--   Its memoryless $n$-fold version acts on complex $2^n\times2^n$ matrices, whose rows and columns are indexed by bit strings $x=(x_1,\dots,x_n)\in\{0,1\}^n$, by $\mathcal N^{\otimes n}_{\gamma,\nu}(\rho)=\sum_{r\in\{0,1,2,3\}^n}K_r\,\rho\,K_r^{*}$ with $K_r=K_{r_1}\otimes\cdots\otimes K_{r_n}$.
--
--   Codes and rates are defined operationally. An $n$-use code $C$ consists of a number $M\ge1$ of messages, encoding states $\rho_1,\dots,\rho_M$ (arbitrary density matrices on $n$ qubits, possibly entangled across the channel uses) and a decoding POVM $D_1,\dots,D_M$ (positive semidefinite $2^n\times2^n$ matrices with $\sum_mD_m=I$). Its average error probability is
--
--   $$
--   P_e(C)=1-\frac1M\sum_{m=1}^M\operatorname{Re}\operatorname{tr}\bigl(D_m\,\mathcal N^{\otimes n}_{\gamma,\nu}(\rho_m)\bigr).
--   $$
--
--   A real number $R$ is an achievable rate if there are codes $C_n$, one for each $n\in\mathbb{N}$, with $M_n$ messages, such that $P_e(C_n)\to0$ as $n\to\infty$ and, for every $\varepsilon>0$, $R-\varepsilon\le\frac{\log_2M_n}{n}$ for all sufficiently large $n$; no entanglement assistance or feedback is involved. Finally let $h(x)=-x\log x-(1-x)\log(1-x)$ be the binary entropy (natural logarithm), $g(u)=h\bigl(\tfrac{1+\sqrt{1-4u}}{2}\bigr)$, $v_{\gamma,\nu}(q)=\gamma\nu(1-\nu)+\gamma(1-\gamma)(q-\nu)^2$ and $F_{\gamma,\nu}(q)=h\bigl((1-\gamma)q+\gamma\nu\bigr)-g\bigl(v_{\gamma,\nu}(q)\bigr)$, and let $p\in[0,1]$ maximize $F_{\gamma,\nu}$ on $[0,1]$.
--
--   **Theorem.** Every achievable rate $R$ satisfies
--
--   $$
--   R\le\frac{F_{\gamma,\nu}(p)}{\log2}.
--   $$
--
--   This is the weak converse of the classical capacity theorem for the generalized amplitude-damping channel: no sequence of codes with vanishing average error, even with entangled encodings and collective decoding, transmits more than $F_{\gamma,\nu}(p)/\log2$ bits per channel use. The bound equals the one-shot Holevo quantity of the channel (the largest Holevo information, in bits, of an ensemble of single-qubit inputs), so together with an achievability statement it identifies the operational capacity with this single-letter quantity.
--
--   **Formalization Note** `Achievable` asks for a family `C : (n : Nat) -> Code n` whose `averageError` tends to $0$ and such that for every $\varepsilon>0$ the inequality $R-\varepsilon\le\log M_n/\log2/n$ (written with `Real.log`) holds eventually; this is the eventual lower-bound form of a liminf condition on the rate. At $n=0$ Lean's division by zero gives $0$, which is irrelevant because only large $n$ matter. `Maximizes γ ν p` is the maximizer hypothesis and `objective` is $F_{\gamma,\nu}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/CapacityConverse.lean#L107-L137

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

open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter

theorem OAI.GAD.achievable_upper (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p R : ℝ} (hp : Maximizes γ ν p)
    (hR : Achievable γ ν R) : R ≤ objective γ ν p/Real.log 2 := by sorry
