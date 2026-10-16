-- Prove2me | Theorems.Thm_OAI_GAD_thermal_entropy
-- name    : OAI.GAD.thermal_entropy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:23:22.66119+00:00
-- url     : https://prove2.me/theorems/cb0c83a5-7869-40ae-94ed-7a70adba8f85
-- title:
--   Entropy lower bound for a two-block matrix built from two Gram matrices
-- statement:
--   Let $\iota,\kappa$ be finite index sets and let $X,Y\in\mathbb{C}^{\iota\times\kappa}$ have unit Frobenius norm, $\operatorname{Tr}(XX^*)=\operatorname{Tr}(YY^*)=1$. For real numbers $a,b,c,d,K\ge0$ with
--   $$a+b+c+d=1,\qquad ad-bc=K^2,$$
--   consider the $2\times2$ block matrix, indexed by two copies of $\iota$,
--   $$T=\begin{pmatrix}a\,XX^*+b\,YY^* & K\,XY^*\\ K\,YX^* & c\,XX^*+d\,YY^*\end{pmatrix}.$$
--   Write $S(M)=\sum_j\eta(\lambda_j(M))$ for the von Neumann entropy of a positive semidefinite matrix $M$, with $\eta(x)=-x\log x$ (natural logarithm); let $h(p)=-p\log p-(1-p)\log(1-p)$ be the binary entropy, and set
--   $$g(u)=h\Bigl(\frac{1+\sqrt{1-4u}}{2}\Bigr),\qquad u=(a+b)(c+d)-K^2 .$$
--   Then:
--
--   1. $T$ is a density matrix: $T$ is positive semidefinite and $\operatorname{Tr}T=1$.
--   2. $0\le u\le\frac14$.
--   3. The entropy of $T$ satisfies
--
--   $$
--   (a+c)\,S(XX^*)+(b+d)\,S(YY^*)+g(u)\le S(T).
--   $$
--
--   The bound holds for all admissible coefficients, including the boundary cases $b=0$ or $c=0$. In the analysis of the generalized amplitude-damping channel, the output of the $(n+1)$-fold channel on a pure input, written in blocks according to one qubit, has exactly this form, and the inequality gives a recursive lower bound for output entropies of pure inputs, with $g(u)$ as the one-qubit contribution.
--
--   **Formalization Note** $T$ is `thermal X Y a b c d K`, built with `Matrix.fromBlocks` on `ι ⊕ ι`. The normalizations are `mass X = 1` and `mass Y = 1`, where `mass X` is the real part of the trace of `gram X = X * Xᴴ`. Being a density matrix is `IsState` (positive semidefinite with trace $1$), $h$ is `Real.binEntropy`, $u$ is introduced by a `let`, and `entropy` is the real part of the trace of `cfc Real.negMulLog`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/ThermalEntropy.lean#L119-L213

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

open OAI OAI.GAD
universe u_1 u_2 u_3 u_4
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_3} {κ : Type u_4} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem OAI.GAD.thermal_entropy (X Y : Matrix ι κ ℂ) (hX : mass X = 1) (hY : mass Y = 1)
    {a b c d K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hK : 0 ≤ K) (hs : a+b+c+d=1) (hk : a*d-b*c=K^2) :
    let u := (a+b)*(c+d)-K^2
    IsState (thermal X Y a b c d K) ∧ u ∈ Set.Icc (0 : ℝ) (1/4) ∧
      (a+c)*entropy (gram X)+(b+d)*entropy (gram Y)+g u ≤ entropy (thermal X Y a b c d K) := by sorry
