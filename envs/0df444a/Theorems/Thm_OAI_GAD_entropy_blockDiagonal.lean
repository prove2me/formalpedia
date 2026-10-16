-- Prove2me | Theorems.Thm_OAI_GAD_entropy_blockDiagonal
-- name    : OAI.GAD.entropy_blockDiagonal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:33:11.475984+00:00
-- url     : https://prove2.me/theorems/a04a136d-4222-4835-8ca4-c42ce5dd313c
-- title:
--   Entropy is additive over the blocks of a block-diagonal Hermitian matrix
-- statement:
--   Let $\iota$ and $\mu$ be finite index sets and let $(A_m)_{m\in\mu}$ be Hermitian matrices in $\mathbb{C}^{\iota\times\iota}$. Their block-diagonal sum $\bigoplus_mA_m$ is the matrix indexed by $\iota\times\mu$ with entries
--   $$\Big(\bigoplus_{m}A_m\Big)_{(i,m),(j,m')}=\begin{cases}(A_m)_{ij},&m=m',\\0,&m\ne m'.\end{cases}$$
--   For a Hermitian matrix $H$ with eigenvalues $\lambda_1,\dots,\lambda_N$ (with multiplicity) set $S(H)=\sum_k\eta(\lambda_k)$, where $\eta(0)=0$ and $\eta(x)=-x\log|x|$ for $x\ne0$ (natural logarithm); for a density matrix this is the von Neumann entropy. Then
--   $$
--   S\Big(\bigoplus_{m\in\mu}A_m\Big)=\sum_{m\in\mu}S(A_m).
--   $$
--
--   The entropy functional depends only on the spectrum, and the spectrum of a block-diagonal matrix is the union, with multiplicities, of the spectra of its blocks. The identity is used to compute entropies of mixtures of states supported on mutually orthogonal blocks, as they arise in Naimark-dilation arguments.
--
--   **Formalization Note** The block-diagonal matrix is Mathlib's `Matrix.blockDiagonal A`. The entropy is `entropy`, the real part of the trace of `cfc Real.negMulLog`; because Mathlib's logarithm satisfies $\log x=\log|x|$, this is the functional $S$ above, and the statement holds for all Hermitian blocks, not only positive semidefinite ones.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/BlockFactors.lean#L29-L47

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

open OAI OAI.GAD
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_1} {μ : Type u_2} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

theorem OAI.GAD.entropy_blockDiagonal (A : μ → Matrix ι ι ℂ) (hA : ∀ m, (A m).IsHermitian) :
    entropy (Matrix.blockDiagonal A)=∑ m, entropy (A m) := by sorry
