-- Prove2me | Theorems.Thm_OAI_GAD_holevo_formula
-- name    : OAI.GAD.holevo_formula
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:43:55.386048+00:00
-- url     : https://prove2.me/theorems/eaa4cea8-5e68-4d8e-a198-3574845e23dd
-- title:
--   Closed single-letter formula for the $n$-use Holevo quantity of the generalized amplitude-damping channel
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
--   Let $S(\sigma)=-\operatorname{tr}\sigma\log\sigma$ be the von Neumann entropy (natural logarithm, $0\log0=0$), $h(x)=-x\log x-(1-x)\log(1-x)$ the binary entropy, and define for real $u,q$
--
--   $$
--   g(u)=h\Bigl(\frac{1+\sqrt{1-4u}}{2}\Bigr),\qquad v_{\gamma,\nu}(q)=\gamma\nu(1-\nu)+\gamma(1-\gamma)(q-\nu)^2,\qquad F_{\gamma,\nu}(q)=h\bigl((1-\gamma)q+\gamma\nu\bigr)-g\bigl(v_{\gamma,\nu}(q)\bigr).
--   $$
--
--   A finite ensemble $E$ of $n$-qubit states consists of weights $w_1,\dots,w_k\ge0$ with $\sum_aw_a=1$ ($k\in\mathbb{N}$) and density matrices $\rho_1,\dots,\rho_k$ on $n$ qubits, with no product or purity restriction. Its Holevo value in bits is
--
--   $$
--   \chi(E)=\frac{1}{\log2}\Bigl[S\Bigl(\sum_aw_a\,\mathcal N^{\otimes n}_{\gamma,\nu}(\rho_a)\Bigr)-\sum_aw_a\,S\bigl(\mathcal N^{\otimes n}_{\gamma,\nu}(\rho_a)\bigr)\Bigr],
--   $$
--
--   and the $n$-use Holevo quantity $\chi_n(\gamma,\nu)$ is the supremum of $\chi(E)$ over all such ensembles.
--
--   **Theorem.** Let $p\in[0,1]$ maximize $F_{\gamma,\nu}$ on $[0,1]$, i.e. $F_{\gamma,\nu}(q)\le F_{\gamma,\nu}(p)$ for all $q\in[0,1]$. Then for every $n\in\mathbb{N}$
--
--   $$
--   \chi_n(\gamma,\nu)=\frac{n}{\log2}\,F_{\gamma,\nu}(p).
--   $$
--
--   Since a maximizer always exists ($F_{\gamma,\nu}$ is continuous on the compact interval $[0,1]$), this gives the additivity $\chi_n(\gamma,\nu)=n\,\chi_1(\gamma,\nu)$ of the Holevo quantity of the GAD channel over arbitrary, possibly entangled, ensembles, together with the explicit one-shot value $\chi_1(\gamma,\nu)=F_{\gamma,\nu}(p)/\log2$ obtained from a one-dimensional optimization.
--
--   **Formalization Note** `holevo γ ν n` is defined as `sSup` of the range of `ensembleValue`; this range is nonempty and bounded above, so `sSup` is the genuine supremum. `Maximizes γ ν p` is the maximizer hypothesis and `objective` is $F_{\gamma,\nu}$. Entropies use natural logarithms, which is why the formula carries the factor $1/\log2$. The case $n=0$ is included; then both sides are $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/Holevo.lean#L10-L23

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

open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

theorem OAI.GAD.holevo_formula (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : Maximizes γ ν p) (n : ℕ) :
    holevo γ ν n = (n:ℝ)/Real.log 2*objective γ ν p := by sorry
