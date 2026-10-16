-- Prove2me | Theorems.Thm_OAI_GAD_ensemble_nats_upper
-- name    : OAI.GAD.ensemble_nats_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:40:52.572486+00:00
-- url     : https://prove2.me/theorems/73ad7b37-f94e-4c30-894c-76eb96be4b38
-- title:
--   Holevo quantity of every $n$-qubit ensemble through the GAD channel is at most $n$ times the single-letter maximum
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
--   Let $p\in[0,1]$ be a maximizer of $F_{\gamma,\nu}$ on $[0,1]$, that is, $F_{\gamma,\nu}(q)\le F_{\gamma,\nu}(p)$ for all $q\in[0,1]$.
--
--   **Theorem.** For every $n\in\mathbb{N}$ and every finite ensemble of $n$-qubit states, namely weights $w_1,\dots,w_k\ge0$ with $\sum_aw_a=1$ and density matrices $\rho_1,\dots,\rho_k$ (positive semidefinite with trace one, and otherwise arbitrary: possibly mixed, entangled and not of product form),
--
--   $$
--   S\Bigl(\sum_{a=1}^kw_a\,\mathcal N^{\otimes n}_{\gamma,\nu}(\rho_a)\Bigr)-\sum_{a=1}^kw_a\,S\bigl(\mathcal N^{\otimes n}_{\gamma,\nu}(\rho_a)\bigr)\le n\,F_{\gamma,\nu}(p).
--   $$
--
--   The left-hand side is the Holevo quantity, measured in nats, of the output ensemble obtained by sending the input ensemble through $n$ uses of the channel, and the theorem bounds it by $n$ times the single-letter maximum. Dividing by $\log2$ gives the upper half of the closed formula for the $n$-use Holevo quantity in bits; applied to the uniform ensemble of the codewords of a code, it supplies the entropy estimate in the converse of the classical capacity theorem.
--
--   **Formalization Note** The ensemble is a structure `Ensemble n` consisting of a size $k$, nonnegative weights summing to $1$ and states; in the average output the real weights are coerced to complex scalars. The hypothesis `Maximizes` encodes that $p$ maximizes `objective` $=F_{\gamma,\nu}$ on $[0,1]$, and all entropies use the natural logarithm (`Real.binEntropy`, `Real.negMulLog`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/EnsembleBounds.lean#L112-L145

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

open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

theorem OAI.GAD.ensemble_nats_upper (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (E : Ensemble n) {p : ℝ} (hp : Maximizes γ ν p) :
    entropy (∑ a, (E.weight a : ℂ) • channel γ ν n (E.signal a)) -
      (∑ a, E.weight a * entropy (channel γ ν n (E.signal a))) ≤
    (n : ℝ)*objective γ ν p := by sorry
