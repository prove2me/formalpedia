-- Prove2me | Theorems.Thm_OAI_MainGap_ProperlyInfinite_finite_copies
-- name    : OAI.MainGap.ProperlyInfinite.finite_copies
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:13:58.897524+00:00
-- url     : https://prove2.me/theorems/123e04e0-9d25-4c64-8340-0c966954bd99
-- title:
--   A properly infinite element dominates any finite number of diagonal copies of itself
-- statement:
--   Let $A$ be a C*-algebra (not necessarily unital). For $m,n\in\mathbb{N}$ let $M_{m\times n}(A)$ be the $m\times n$ matrices with entries in $A$, and let $M_n(A)=M_{n\times n}(A)$ carry its C*-algebra norm. For $d\in M_n(A)$ and $v\in M_m(A)$ write $d\precsim v$ ($d$ is *finitely Cuntz-below* $v$) if there is a sequence $(r_j)_{j\in\mathbb{N}}$ in $M_{m\times n}(A)$ such that $r_j^{*}\,v\,r_j\to d$ in norm as $j\to\infty$. For $h\in A$ let $\operatorname{diag}_n(h)\in M_n(A)$ be the diagonal matrix all of whose diagonal entries equal $h$, and let $(h)\in M_1(A)$ be the $1\times 1$ matrix with entry $h$. The element $h$ is called *properly infinite* if $\operatorname{diag}_2(h)\precsim (h)$.
--
--   **Theorem.** If $h\in A$ is properly infinite, then for every $n\in\mathbb{N}$
--
--   $$
--   \operatorname{diag}_n(h)=\begin{pmatrix} h & & \\ & \ddots & \\ & & h\end{pmatrix}\precsim (h).
--   $$
--
--   Concretely: there are rows $(r_{j,1},\dots,r_{j,n})\in M_{1\times n}(A)$ such that $r_{j,k}^{*}\,h\,r_{j,l}\to\delta_{kl}\,h$ as $j\to\infty$, for all $1\le k,l\le n$.
--
--   Proper infiniteness only asks for room for two copies of $h$ underneath $h$; this result upgrades it to any finite number of copies. It is what makes it possible to place $n$ mutually orthogonal copies of cut-downs of $h$ inside the hereditary subalgebra of $h$, for every $n$.
--
--   **Formalization Note** The relation $d\precsim v$ is `FiniteCuntzLE d v`, $\operatorname{diag}_n(h)$ is `diagonalCorner n h`, $(h)$ is `scalarCorner h`, and `ProperlyInfinite h` is the matrix-level condition `FiniteCuntzLE (doubleCorner h) (scalarCorner h)`. The case $n=0$ is included (there $M_0(A)$ is the zero space and the claim is trivial). No positivity of $h$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Comparison.lean#L279-L295

import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.positivityOrder
attribute [local instance] OAI.MainGap.positivityStarOrder
variable {A : Type*} [NonUnitalCStarAlgebra A]

theorem OAI.MainGap.ProperlyInfinite.finite_copies {h : A} (hh : ProperlyInfinite h) (n : ℕ) :
    FiniteCuntzLE (diagonalCorner n h) (scalarCorner h) := by sorry
