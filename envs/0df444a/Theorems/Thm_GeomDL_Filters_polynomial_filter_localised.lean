-- Prove2me | Theorems.Thm_GeomDL_Filters_polynomial_filter_localised
-- name    : GeomDL.Filters.polynomial_filter_localised
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T18:14:18.824734+00:00
-- url     : https://prove2.me/theorems/6242e737-bdd5-45a6-9c32-13e9c46e0678
-- title:
--   §4.6, p. 65 — a polynomial filter of degree r is localised in r-hop neighbourhood
-- statement:
--   Let $G$ be a simple graph on the nodes $\{1,\dots,n\}$, and let $W\in\mathbb R^{n\times n}$ be a weight matrix supported on the edges of $G$: $w_{uv}\neq 0$ with $u\neq v$ implies that $u$ and $v$ are adjacent in $G$. Let $\Delta=D-W$ be the Laplacian (24), $r\ge 0$, and $\alpha_0,\dots,\alpha_r\in\mathbb R$. Fix a node $u$ and two feature matrices $X,X'\in\mathbb R^{n\times d}$ whose rows agree at every node within $r$ hops of $u$ (every $v$ joined to $u$ by a walk of length at most $r$). Then
--   $$\Big(\sum_{k=0}^r\alpha_k\Delta^kX\Big)_u=\Big(\sum_{k=0}^r\alpha_k\Delta^kX'\Big)_u .$$
--
--   That is, the output of a degree-$r$ polynomial filter at $u$ depends only on the features in the $r$-hop neighbourhood of $u$. This is what makes polynomial spectral filters on graphs local, in contrast with general spectral filters and with rational filters, which have exponential decay but not local support.
--
--   **Formalization Note** The book's graph is the graph of the weights; here the weights may live on any graph $G$ containing their support (diagonal weights are allowed and cancel in $\Delta$), and $W$ need not be symmetric. The book's setting $W=W^\top$, $G$ the graph of $W$, is a special case.
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning (arXiv:2104.13478v2), §4.6, p. 65, "Furthermore, since the Laplacian is local, a polynomial filter of degree r is localised in r-hop neighbourhood."

import Mathlib
import Definitions.Def_GeomDL_Filters_Defs

namespace GeomDL.Filters
open Matrix
/-- §4.6, p. 65: "since the Laplacian is local, a polynomial filter of degree `r` is localised in
`r`-hop neighbourhood". Let the weights `W` be supported on the edges of the graph `G`
(`w_uv ≠ 0` with `u ≠ v` forces `u ∼ v`). If two feature matrices `X, X'` agree on every node
within `r` hops of `u`, then `p̂(Δ)X` and `p̂(Δ)X'` agree at `u`, for every choice of
coefficients `α₀, …, α_r`. -/
theorem polynomial_filter_localised {n d : ℕ} (G : SimpleGraph (Fin n))
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : ∀ u v, u ≠ v → W u v ≠ 0 → G.Adj u v)
    (r : ℕ) (α : Fin (r + 1) → ℝ) (X X' : Matrix (Fin n) (Fin d) ℝ) (u : Fin n)
    (hX : ∀ v, WithinHops G r u v → X v = X' v) :
    (polyFilter W r α * X) u = (polyFilter W r α * X') u := by sorry
end GeomDL.Filters
