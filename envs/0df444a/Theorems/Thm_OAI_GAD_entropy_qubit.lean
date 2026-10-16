-- Prove2me | Theorems.Thm_OAI_GAD_entropy_qubit
-- name    : OAI.GAD.entropy_qubit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:42:23.683651+00:00
-- url     : https://prove2.me/theorems/bad73747-d08e-4eaa-9b35-970ac6e66bd2
-- title:
--   Entropy of a Hermitian trace-one $2\times2$ matrix as a function of its determinant
-- statement:
--   Let $P$ be a complex $2\times2$ Hermitian matrix with $\operatorname{tr}P=1$, and let $\lambda_1,\lambda_2\in\mathbb{R}$ be its eigenvalues. Its von Neumann entropy is $S(P)=\eta(\lambda_1)+\eta(\lambda_2)$, where $\eta(t)=-t\log t$ (natural logarithm, $\eta(0)=0$). Let $h(x)=-x\log x-(1-x)\log(1-x)=\eta(x)+\eta(1-x)$ be the binary entropy and $g(u)=h\bigl(\tfrac{1+\sqrt{1-4u}}{2}\bigr)$. Since $P$ is Hermitian, $\det P$ is a real number.
--
--   **Theorem.**
--
--   $$
--   S(P)=g(\det P)=h\Bigl(\frac{1+\sqrt{1-4\det P}}{2}\Bigr).
--   $$
--
--   For a qubit density matrix the eigenvalues are $\frac{1\pm\sqrt{1-4\det P}}{2}$, so the entropy depends only on the determinant, and $g$ is the function converting the determinant into the entropy. This is how single-qubit output entropies are evaluated in the analysis of the generalized amplitude-damping channel, where the output produced from a pure qubit input has a determinant that is an explicit quadratic polynomial in the input population.
--
--   **Formalization Note** Positivity of $P$ is not assumed. With Lean's conventions $\log0=0$ and $\log t=\log|t|$ the functions $\eta$ and $h$ are defined on all of $\mathbb{R}$ and $h(t)=\eta(t)+\eta(1-t)$ holds for every real $t$, so the identity is valid for every Hermitian trace-one matrix; for density matrices it is the usual statement. The determinant enters as the real part `P.det.re`, and $1-4\det P=(\lambda_1-\lambda_2)^2\ge0$, so `Real.sqrt` is the ordinary square root here.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/PhaseStates.lean#L12-L38

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

open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

theorem OAI.GAD.entropy_qubit {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P.IsHermitian)
    (htr : P.trace=1) : entropy P = g P.det.re := by sorry
