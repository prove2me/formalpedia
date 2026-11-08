-- Prove2me | Theorems.Thm_HigherComm_centralAt_iff_le
-- name    : HigherComm.centralAt_iff_le
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T16:26:26.725183+00:00
-- url     : https://prove2.me/theorems/c11e5f87-d40d-4f38-931f-3827fbe77534
-- title:
--   Centrality is upward closed: C(T; delta) iff [T] <= delta
-- statement:
--   $L$ is a signature without relation symbols and $M$ an $L$-algebra; congruences are compatible equivalence relations, ordered by inclusion. $m_0,\dots,m_n$ are Day terms for $M$: 4-ary terms with $m_e(x,y,y,x)=x$, $m_0=x$, $m_n=u$, $m_e(x,x,u,u)=m_{e+1}(x,x,u,u)$ ($e$ even), $m_e(x,y,y,u)=m_{e+1}(x,y,y,u)$ ($e$ odd), holding for all elements of $M$. For congruences $T=(\theta_0,\dots,\theta_{k-1})$ with $k\ge2$, a $T$-matrix is a map $h:\{0,1\}^k\to M$, $h(f)=t(\mathbf x_0,\dots,\mathbf x_{k-1})$ with $\mathbf x_i=\mathbf a_i$ if $f(i)=0$ and $\mathbf x_i=\mathbf b_i$ if $f(i)=1$, for a polynomial $t$ (a term with constants from $M$) in blocks of variables of arbitrary arities and tuples $\mathbf a_i\equiv_{\theta_i}\mathbf b_i$. A $(j)$-line is a pair of vertices differing only in coordinate $j$; the pivot $(j)$-line has all other coordinates $1$, the others are supporting. $C(T;j;\delta)$: in every $T$-matrix, if all supporting $(j)$-lines are $\delta$-pairs then so is the pivot $(j)$-line. $[\theta_0,\dots,\theta_k]$ is the intersection of all congruences $\delta$ with $C(T;k;\delta)$ (last coordinate). For $k\ge1$, congruences $T=(\theta_0,\dots,\theta_k)$, any coordinate $j$ and any congruence $\delta$: $C(T;j;\delta)$ holds iff $[\theta_0,\dots,\theta_k]\le\delta$.
-- source:
--   A. Moorhead, Higher commutator theory for congruence modular varieties, J. Algebra 513 (2018) 133-158, https://doi.org/10.1016/j.jalgebra.2018.07.026 (arXiv:1610.07087), Thm 4.4(2)

import Definitions.Def_HigherComm_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace HigherComm

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]

variable [L.IsAlgebraic]

/-- Moorhead, Thm 4.4(2).  In an algebra with Day terms, `C(T; δ)` holds (at any coordinate
`j`) iff `[T] ≤ δ`. -/
theorem centralAt_iff_le {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    (T : Fin (k + 2) → Congruence (L := L) M) (j : Fin (k + 2)) (δ : Congruence (L := L) M) :
    CentralAt T j δ ↔ higherComm T ≤ δ := by sorry

end HigherComm
