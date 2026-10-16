-- Prove2me | Theorems.Thm_OAI_GAD_channel_population
-- name    : OAI.GAD.channel_population
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:40:09.333824+00:00
-- url     : https://prove2.me/theorems/1492e00c-cc23-40f3-aa7b-e672a744d7c0
-- title:
--   Qubit populations relax affinely under the generalized amplitude-damping channel
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
--   A state is a positive semidefinite matrix of trace one. For an $n$-qubit state $\rho$ the population of qubit $j$ is $\pi_j(\rho)=\sum_{x\in\{0,1\}^n:\ x_j=1}\rho_{xx}$, the probability of reading $1$ when qubit $j$ is measured in the computational basis.
--
--   **Theorem.** For every $n\in\mathbb{N}$, every $n$-qubit state $\rho$ and every qubit $j\in\{1,\dots,n\}$,
--
--   $$
--   \pi_j\bigl(\mathcal N^{\otimes n}_{\gamma,\nu}(\rho)\bigr)=(1-\gamma)\,\pi_j(\rho)+\gamma\nu .
--   $$
--
--   Each population therefore moves towards $\nu$, the population of the channel's fixed point when $\gamma>0$, by the factor $1-\gamma$, independently of the other qubits and of any correlations or entanglement in the input. The identity turns input populations into exact output populations; it is used to bound the output entropy from above by the sum of the binary entropies of the output populations $(1-\gamma)\pi_j(\rho)+\gamma\nu$, which is where the argument $(1-\gamma)q+\gamma\nu$ of the single-letter capacity objective comes from.
--
--   **Formalization Note** Qubits are indexed by `Fin n` (numbered $1,\dots,n$ above), so for $n=0$ the statement is vacuous. `IsState` means positive semidefinite with trace $1$, and `matrixPopulation P j` sums the real parts of the diagonal entries $P_{xx}$ with $x_j=1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/OutputEntropy.lean#L181-L196

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

theorem OAI.GAD.channel_population (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} {P : QMatrix n} (hP : IsState P) (j : Fin n) :
    matrixPopulation (channel γ ν n P) j = (1-γ)*matrixPopulation P j+γ*ν := by sorry
