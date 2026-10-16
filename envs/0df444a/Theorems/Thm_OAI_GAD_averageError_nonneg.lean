-- Prove2me | Theorems.Thm_OAI_GAD_averageError_nonneg
-- name    : OAI.GAD.averageError_nonneg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:02:09.047722+00:00
-- url     : https://prove2.me/theorems/3089d39d-25b5-4e83-bb13-c1b7d3618012
-- title:
--   Average decoding error over the generalized amplitude-damping channel is nonnegative
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
--   **Theorem.** Let $\gamma,\nu\in[0,1]$, let $n$ be any natural number and let $C$ be any $n$-use code with $M$ messages. Then
--
--   $$
--   \bar e(C)\ge0,\qquad\text{equivalently}\qquad\frac1M\sum_{m=1}^{M}\operatorname{Re}\operatorname{tr}\bigl(D_m\,\mathcal N^{\otimes n}(\rho_m)\bigr)\le1 .
--   $$
--
--   The average success probability of a code is at most one. This lower bound is what makes squeeze arguments work: once an upper bound on the error of a sequence of codes tends to $0$, the errors themselves tend to $0$. The restriction $\gamma,\nu\in[0,1]$ is what makes $\mathcal N^{\otimes n}$ map states to states.
--
--   **Formalization Note** The code is the structure `Code n`, whose fields encode $M\ge1$, the encoding states and the POVM, and $\bar e$ is `averageError γ ν C`. For $n=0$ the system is one-dimensional and the statement still holds.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/CodingAsymptotics.lean#L12-L28

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

theorem OAI.GAD.averageError_nonneg (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (C : Code n) :
    0 ≤ averageError γ ν C := by sorry
