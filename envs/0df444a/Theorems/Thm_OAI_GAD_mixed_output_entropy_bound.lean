-- Prove2me | Theorems.Thm_OAI_GAD_mixed_output_entropy_bound
-- name    : OAI.GAD.mixed_output_entropy_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:39:04.172749+00:00
-- url     : https://prove2.me/theorems/c68122ff-6d35-43db-836e-1030c7c7f532
-- title:
--   Population lower bound for the output entropy of the $n$-qubit generalized amplitude-damping channel
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
--   A state (density matrix) is a positive semidefinite matrix of trace one. For an $n$-qubit state $\rho$ the population of qubit $j$ is $\pi_j(\rho)=\sum_{x\in\{0,1\}^n:\ x_j=1}\rho_{xx}$, the probability of reading $1$ when qubit $j$ is measured in the computational basis. Let $S(\sigma)=-\operatorname{tr}\sigma\log\sigma$ be the von Neumann entropy (natural logarithm, $0\log0=0$), $h(x)=-x\log x-(1-x)\log(1-x)$ the binary entropy, and
--
--   $$
--   g(u)=h\Bigl(\frac{1+\sqrt{1-4u}}{2}\Bigr),\qquad v_{\gamma,\nu}(p)=\gamma\nu(1-\nu)+\gamma(1-\gamma)(p-\nu)^2 .
--   $$
--
--   **Theorem.** For every $n\in\mathbb{N}$ and every $n$-qubit state $\rho$,
--
--   $$
--   \sum_{j=1}^{n}g\bigl(v_{\gamma,\nu}(\pi_j(\rho))\bigr)\le S\bigl(\mathcal N^{\otimes n}_{\gamma,\nu}(\rho)\bigr).
--   $$
--
--   The number $g(v_{\gamma,\nu}(p))$ is the entropy of the single-qubit output $\mathcal N_{\gamma,\nu}(|\phi\rangle\langle\phi|)$ of a pure input $\phi$ with population $p$, because $v_{\gamma,\nu}(p)$ is the determinant of that output. The theorem therefore says that no input, however mixed or entangled across the $n$ qubits, produces less output entropy than the sum of these single-qubit values computed from its populations. It is the lower half of the entropy bookkeeping behind the additivity of the Holevo quantity of the GAD channel: combined with a subadditivity upper bound for the average output state, it bounds the Holevo quantity of every $n$-qubit ensemble by $n$ times a single-letter maximum.
--
--   **Formalization Note** Matrices are indexed by `Fin n -> Fin 2` and qubits by `Fin n` (numbered $1,\dots,n$ above). `IsState` means positive semidefinite with trace $1$, `matrixPopulation P j` is $\pi_j$ (a sum of real parts of diagonal entries), and `entropy` is the real part of the trace of $\eta(\sigma)$ formed with the continuous functional calculus, where $\eta(t)=-t\log t$. The case $n=0$ is included, with an empty sum on the left.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/OutputEntropy.lean#L58-L89

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

theorem OAI.GAD.mixed_output_entropy_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) {P : QMatrix n} (hP : IsState P) :
    ∑ j, g (v γ ν (matrixPopulation P j)) ≤ entropy (channel γ ν n P) := by sorry
