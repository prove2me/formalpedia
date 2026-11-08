-- Prove2me | Theorems.Thm_HigherComm_centralAt_iff_twoTerm
-- name    : HigherComm.centralAt_iff_twoTerm
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T16:27:03.176208+00:00
-- url     : https://prove2.me/theorems/527266d3-cebb-4c01-8a7c-d626770e660d
-- title:
--   Equivalence with the two-term condition
-- statement:
--   $L$ is a signature without relation symbols and $M$ an $L$-algebra; congruences are compatible equivalence relations, ordered by inclusion. $m_0,\dots,m_n$ are Day terms for $M$: 4-ary terms with $m_e(x,y,y,x)=x$, $m_0=x$, $m_n=u$, $m_e(x,x,u,u)=m_{e+1}(x,x,u,u)$ ($e$ even), $m_e(x,y,y,u)=m_{e+1}(x,y,y,u)$ ($e$ odd), holding for all elements of $M$. For congruences $T=(\theta_0,\dots,\theta_{k-1})$ with $k\ge2$, a $T$-matrix is a map $h:\{0,1\}^k\to M$, $h(f)=t(\mathbf x_0,\dots,\mathbf x_{k-1})$ with $\mathbf x_i=\mathbf a_i$ if $f(i)=0$ and $\mathbf x_i=\mathbf b_i$ if $f(i)=1$, for a polynomial $t$ (a term with constants from $M$) in blocks of variables of arbitrary arities and tuples $\mathbf a_i\equiv_{\theta_i}\mathbf b_i$. A $(j)$-line is a pair of vertices differing only in coordinate $j$; the pivot $(j)$-line has all other coordinates $1$, the others are supporting. $C(T;j;\delta)$: in every $T$-matrix, if all supporting $(j)$-lines are $\delta$-pairs then so is the pivot $(j)$-line. $[\theta_0,\dots,\theta_k]$ is the intersection of all congruences $\delta$ with $C(T;k;\delta)$ (last coordinate). $C_{tt}(T;\delta)$: for all $T$-matrices $h,g$, if $h(f)\equiv_\delta g(f)$ for every vertex $f$ other than the all-ones vertex, then also at the all-ones vertex. For $T=(\theta_0,\dots,\theta_k)$ with $k\ge1$, any coordinate $j$ and any $\delta$: $C(T;j;\delta)$ holds iff $C_{tt}(T;\delta)$ holds.
-- source:
--   A. Moorhead, Higher commutator theory for congruence modular varieties, J. Algebra 513 (2018) 133-158, https://doi.org/10.1016/j.jalgebra.2018.07.026 (arXiv:1610.07087), Prop 6.4

import Definitions.Def_HigherComm_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace HigherComm

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M] [L.IsAlgebraic]

/-- Moorhead, Prop 6.4 (two-term condition).  In an algebra with Day terms, `C(T; δ)` (at any
coordinate `j`) holds iff the two-term condition `C_tt(T; δ)` holds. -/
theorem centralAt_iff_twoTerm {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    (T : Fin (k + 2) → Congruence (L := L) M) (j : Fin (k + 2)) (δ : Congruence (L := L) M) :
    CentralAt T j δ ↔ TwoTermCentral T δ := by sorry

end HigherComm
