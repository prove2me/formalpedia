-- Prove2me | Theorems.Thm_HigherComm_additivity
-- name    : HigherComm.additivity
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T16:26:38.299548+00:00
-- url     : https://prove2.me/theorems/a95c3ee8-a985-4a5d-8498-c7c34119964f
-- title:
--   Additivity of the higher commutator
-- statement:
--   $L$ is a signature without relation symbols and $M$ an $L$-algebra; congruences are compatible equivalence relations, ordered by inclusion. $m_0,\dots,m_n$ are Day terms for $M$: 4-ary terms with $m_e(x,y,y,x)=x$, $m_0=x$, $m_n=u$, $m_e(x,x,u,u)=m_{e+1}(x,x,u,u)$ ($e$ even), $m_e(x,y,y,u)=m_{e+1}(x,y,y,u)$ ($e$ odd), holding for all elements of $M$. For congruences $T=(\theta_0,\dots,\theta_{k-1})$ with $k\ge2$, a $T$-matrix is a map $h:\{0,1\}^k\to M$, $h(f)=t(\mathbf x_0,\dots,\mathbf x_{k-1})$ with $\mathbf x_i=\mathbf a_i$ if $f(i)=0$ and $\mathbf x_i=\mathbf b_i$ if $f(i)=1$, for a polynomial $t$ (a term with constants from $M$) in blocks of variables of arbitrary arities and tuples $\mathbf a_i\equiv_{\theta_i}\mathbf b_i$. A $(j)$-line is a pair of vertices differing only in coordinate $j$; the pivot $(j)$-line has all other coordinates $1$, the others are supporting. $C(T;j;\delta)$: in every $T$-matrix, if all supporting $(j)$-lines are $\delta$-pairs then so is the pivot $(j)$-line. $[\theta_0,\dots,\theta_k]$ is the intersection of all congruences $\delta$ with $C(T;k;\delta)$ (last coordinate). For congruences $\theta_0,\dots,\theta_k$ and any family $(\gamma_i)_{i\in I}$ ($I$ arbitrary, possibly empty or infinite): $[\theta_0,\dots,\theta_k,\bigvee_{i\in I}\gamma_i]=\bigvee_{i\in I}[\theta_0,\dots,\theta_k,\gamma_i]$, where $\bigvee$ is the join in the congruence lattice.
-- source:
--   A. Moorhead, Higher commutator theory for congruence modular varieties, J. Algebra 513 (2018) 133-158, https://doi.org/10.1016/j.jalgebra.2018.07.026 (arXiv:1610.07087), Prop 5.1

import Definitions.Def_HigherComm_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace HigherComm

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]

variable [L.IsAlgebraic]

/-- Moorhead, Prop 5.1 (additivity).  In an algebra with Day terms, for congruences
`θ₀, …, θ_k` and any family `(γᵢ)_{i ∈ I}`,
`[θ₀, …, θ_k, ⋁ᵢ γᵢ] = ⋁ᵢ [θ₀, …, θ_k, γᵢ]`. -/
theorem additivity {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    (θ : Fin (k + 1) → Congruence (L := L) M) {I : Type*} (γ : I → Congruence (L := L) M) :
    higherComm (Fin.snoc θ (Congruence.iSup γ)) =
      Congruence.iSup (fun i => higherComm (Fin.snoc θ (γ i))) := by sorry

end HigherComm
