-- Prove2me | Theorems.Thm_HigherComm_shift_rotation
-- name    : HigherComm.shift_rotation
-- status  : Open
-- author  : @Alien60
-- created : 2026-11-06T16:25:49.586815+00:00
-- url     : https://prove2.me/theorems/3329fb01-810f-45f1-997f-57423ce85cf0
-- title:
--   Shift rotation
-- statement:
--   $L$ is a signature without relation symbols and $M$ an $L$-algebra; congruences are compatible equivalence relations, ordered by inclusion. $m_0,\dots,m_n$ are Day terms for $M$: 4-ary terms with $m_e(x,y,y,x)=x$, $m_0=x$, $m_n=u$, $m_e(x,x,u,u)=m_{e+1}(x,x,u,u)$ ($e$ even), $m_e(x,y,y,u)=m_{e+1}(x,y,y,u)$ ($e$ odd), holding for all elements of $M$. For congruences $T=(\theta_0,\dots,\theta_{k-1})$ with $k\ge2$, a $T$-matrix is a map $h:\{0,1\}^k\to M$, $h(f)=t(\mathbf x_0,\dots,\mathbf x_{k-1})$ with $\mathbf x_i=\mathbf a_i$ if $f(i)=0$ and $\mathbf x_i=\mathbf b_i$ if $f(i)=1$, for a polynomial $t$ (a term with constants from $M$) in blocks of variables of arbitrary arities and tuples $\mathbf a_i\equiv_{\theta_i}\mathbf b_i$. A $(j)$-line is a pair of vertices differing only in coordinate $j$; the pivot $(j)$-line has all other coordinates $1$, the others are supporting. For coordinates $j\neq l$ there are maps $R_e$ ($e\le n$) on $\{0,1\}^k\to M$ such that for every $T$-matrix $h$: (0) each $R_e(h)$ is a $T$-matrix; (1) each $(j,l)$-cross-section square $\begin{bmatrix}r&s\\u&v\end{bmatrix}$ of $h$ (rows indexed by coordinate $j$, columns by $l$) becomes $\begin{bmatrix}s&s\\m_e(s,r,u,v)&m_e(s,s,v,v)\end{bmatrix}$ in $R_e(h)$; (2) for every congruence $\delta$, if all supporting $(j)$-lines of $h$ are $\delta$-pairs then all supporting $(l)$-lines of every $R_e(h)$ are; (3) if the supporting $(j)$-line of the $(j,l)$-pivot square of $h$ is a $\delta$-pair, then the pivot $(j)$-line of $h$ is a $\delta$-pair iff the pivot $(l)$-line of $R_e(h)$ is a $\delta$-pair for every $e$.
-- source:
--   A. Moorhead, Higher commutator theory for congruence modular varieties, J. Algebra 513 (2018) 133-158, https://doi.org/10.1016/j.jalgebra.2018.07.026 (arXiv:1610.07087), Lemma 3.1

import Definitions.Def_HigherComm_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace HigherComm

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]

/-- Moorhead, Lemma 3.1 (shift rotation).  Let `m₀, …, mₙ` be Day terms for `M` and
`T = (θ₀, …, θ_{k+1})` (at least two congruences).  For coordinates `j ≠ l` there are maps `R e : M(T) → M(T)`
(`e ≤ n`) such that, for every `h ∈ M(T)`:
(1) each `(j,l)`-cross-section square `[[r, s], [u, v]]` of `h` (rows indexed by `j`, columns
by `l`) becomes `[[s, s], [mₑ(s,r,u,v), mₑ(s,s,v,v)]]` in `R e h`;
(2) if every `(j)`-supporting line of `h` is a `δ`-pair, then every `(l)`-supporting line of
`R e h` is a `δ`-pair;
(3) if the `(j)`-supporting line of the `(j,l)`-pivot square of `h` is a `δ`-pair, then the
`(j)`-pivot line of `h` is a `δ`-pair iff the `(l)`-pivot line of `R e h` is a `δ`-pair for
every `e`. -/
theorem shift_rotation {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    (T : Fin (k + 2) → Congruence (L := L) M) (j l : Fin (k + 2)) (hjl : j ≠ l) :
    ∃ R : Fin (n + 1) → ((Fin (k + 2) → Bool) → M) → ((Fin (k + 2) → Bool) → M),
      ∀ h, IsTMatrix T h →
        (∀ e, IsTMatrix T (R e h)) ∧
        (∀ e (f : Fin (k + 2) → Bool),
          let g := Function.update (Function.update f j false) l false
          let r := h g
          let s := h (Function.update g l true)
          let u := h (Function.update g j true)
          let v := h (Function.update (Function.update g j true) l true)
          R e h f = if f j then (if f l then (m e).realize ![s, s, v, v]
            else (m e).realize ![s, r, u, v]) else s) ∧
        (∀ δ : Congruence (L := L) M, SupportingRel δ h j → ∀ e, SupportingRel δ (R e h) l) ∧
        (∀ δ : Congruence (L := L) M,
          LineRel δ h j (Function.update (fun _ => true) l false) →
            (PivotRel δ h j ↔ ∀ e, PivotRel δ (R e h) l)) := by sorry

end HigherComm
