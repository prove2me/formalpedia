-- Prove2me | Theorems.Thm_OAI_GAD_tensorMatrix_entropy
-- name    : OAI.GAD.tensorMatrix_entropy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:43:23.362358+00:00
-- url     : https://prove2.me/theorems/12d0135f-d0ab-4897-a33c-5fcdb59b9afa
-- title:
--   Von Neumann entropy is additive on tensor products of qubit states
-- statement:
--   Let $n\in\mathbb{N}$ and let $A_1,\dots,A_n$ be complex $2\times2$ density matrices (positive semidefinite with trace one). Their tensor product $A_1\otimes\cdots\otimes A_n$ is the $2^n\times2^n$ matrix whose rows and columns are indexed by bit strings $x,y\in\{0,1\}^n$, with entries
--
--   $$
--   (A_1\otimes\cdots\otimes A_n)_{xy}=\prod_{k=1}^n(A_k)_{x_ky_k}.
--   $$
--
--   Let $S(\sigma)=-\operatorname{tr}\sigma\log\sigma$ denote the von Neumann entropy (natural logarithm, $0\log0=0$).
--
--   **Theorem.**
--
--   $$
--   S(A_1\otimes\cdots\otimes A_n)=\sum_{k=1}^nS(A_k).
--   $$
--
--   For $n=0$ the empty tensor product is the $1\times1$ matrix $(1)$ and both sides are $0$. The theorem is the additivity of von Neumann entropy on product states of $n$ qubits. It is used to evaluate entropies of outputs of memoryless qubit channels on product inputs, since each such output is again a tensor product of single-qubit states.
--
--   **Formalization Note** The tensor product is `tensorMatrix n A` for a family `A : Fin n -> Matrix (Fin 2) (Fin 2) C` (complex entries), defined entrywise by the product formula above on the index type `Fin n -> Fin 2`; the hypothesis is `IsState (A k)` for every `k`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/PhaseProducts.lean#L51-L64

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
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix

theorem OAI.GAD.tensorMatrix_entropy (n : ℕ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ k, IsState (A k)) : entropy (tensorMatrix n A) = ∑ k, entropy (A k) := by sorry
