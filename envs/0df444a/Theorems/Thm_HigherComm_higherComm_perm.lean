-- Prove2me | Theorems.Thm_HigherComm_higherComm_perm
-- name    : HigherComm.higherComm_perm
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T16:26:13.415673+00:00
-- url     : https://prove2.me/theorems/ba6cfffa-8729-40cf-835d-2ba44048596e
-- title:
--   Symmetry of the higher commutator
-- statement:
--   $L$ is a signature without relation symbols and $M$ an $L$-algebra; congruences are compatible equivalence relations, ordered by inclusion. $m_0,\dots,m_n$ are Day terms for $M$: 4-ary terms with $m_e(x,y,y,x)=x$, $m_0=x$, $m_n=u$, $m_e(x,x,u,u)=m_{e+1}(x,x,u,u)$ ($e$ even), $m_e(x,y,y,u)=m_{e+1}(x,y,y,u)$ ($e$ odd), holding for all elements of $M$. For congruences $T=(\theta_0,\dots,\theta_{k-1})$ with $k\ge2$, a $T$-matrix is a map $h:\{0,1\}^k\to M$, $h(f)=t(\mathbf x_0,\dots,\mathbf x_{k-1})$ with $\mathbf x_i=\mathbf a_i$ if $f(i)=0$ and $\mathbf x_i=\mathbf b_i$ if $f(i)=1$, for a polynomial $t$ (a term with constants from $M$) in blocks of variables of arbitrary arities and tuples $\mathbf a_i\equiv_{\theta_i}\mathbf b_i$. A $(j)$-line is a pair of vertices differing only in coordinate $j$; the pivot $(j)$-line has all other coordinates $1$, the others are supporting. $C(T;j;\delta)$: in every $T$-matrix, if all supporting $(j)$-lines are $\delta$-pairs then so is the pivot $(j)$-line. $[\theta_0,\dots,\theta_k]$ is the intersection of all congruences $\delta$ with $C(T;k;\delta)$ (last coordinate). For $k\ge1$, congruences $\theta_0,\dots,\theta_k$ and every permutation $\sigma$ of $\{0,\dots,k\}$: $[\theta_{\sigma(0)},\dots,\theta_{\sigma(k)}]=[\theta_0,\dots,\theta_k]$.
-- source:
--   A. Moorhead, Higher commutator theory for congruence modular varieties, J. Algebra 513 (2018) 133-158, https://doi.org/10.1016/j.jalgebra.2018.07.026 (arXiv:1610.07087), Thm 3.3

import Definitions.Def_HigherComm_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace HigherComm

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]

variable [L.IsAlgebraic]

/-- Moorhead, Thm 3.3 (symmetry), in the form of property (4) of §2: in an algebra with Day
terms, `[θ_{σ(0)}, …, θ_{σ(k+1)}] = [θ₀, …, θ_{k+1}]` for every permutation `σ`. -/
theorem higherComm_perm {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    (T : Fin (k + 2) → Congruence (L := L) M) (σ : Equiv.Perm (Fin (k + 2))) :
    higherComm (T ∘ σ) = higherComm T := by sorry

end HigherComm
