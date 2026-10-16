-- Prove2me | Theorems.Thm_OAI_GAD_concaveOn_entropy
-- name    : OAI.GAD.concaveOn_entropy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:15:45.919404+00:00
-- url     : https://prove2.me/theorems/6ecea109-2d39-487c-87ea-b51fcd74dde6
-- title:
--   Concavity of matrix entropy on the positive semidefinite cone
-- statement:
--   Let $\iota$ be a finite index set and let $\mathcal P=\{A\in\mathbb{C}^{\iota\times\iota}: A\succeq0\}$ be the cone of positive semidefinite matrices, regarded as a subset of the real vector space $\mathbb{C}^{\iota\times\iota}$. For $A\in\mathcal P$ with eigenvalues $\lambda_j\ge0$ let $S(A)=\sum_j\eta(\lambda_j)$, where $\eta(x)=-x\log x$ (natural logarithm, $\eta(0)=0$), be its von Neumann entropy, with no normalization of the trace. Then $S$ is concave on $\mathcal P$: the set $\mathcal P$ is convex, and for all $A,B\in\mathcal P$ and all real $a,b\ge0$ with $a+b=1$,
--
--   $$
--   a\,S(A)+b\,S(B)\le S(aA+bB).
--   $$
--
--   The inequality holds for arbitrary positive semidefinite matrices, not only for density matrices of trace one. Concavity of the von Neumann entropy is the source of Jensen-type bounds for entropies of finite mixtures, such as averaged channel outputs, and it is used to pass from boundary cases of a matrix entropy inequality to convex combinations of them.
--
--   **Formalization Note** The statement is Mathlib's `ConcaveOn ℝ {A | A.PosSemidef} entropy`, which bundles convexity of the domain with the inequality; `entropy A` is the real part of the trace of `cfc Real.negMulLog A`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/SpectralEntropy.lean#L112-L150

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity

open OAI OAI.GAD
universe u_1
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

theorem OAI.GAD.concaveOn_entropy :
    ConcaveOn ℝ {A : Matrix ι ι ℂ | A.PosSemidef} entropy := by sorry
