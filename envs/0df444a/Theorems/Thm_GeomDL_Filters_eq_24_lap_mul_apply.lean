-- Prove2me | Theorems.Thm_GeomDL_Filters_eq_24_lap_mul_apply
-- name    : GeomDL.Filters.eq_24_lap_mul_apply
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T18:14:17.637293+00:00
-- url     : https://prove2.me/theorems/61b15194-82d2-43c2-a4fc-e00d7a9f3e40
-- title:
--   (24), p. 62 — (ΔX)ᵤ = Σ_{v∈𝒩ᵤ} wᵤᵥ(xᵤ − xᵥ) = dᵤxᵤ − Σ_{v∈𝒩ᵤ} wᵤᵥxᵥ for Δ = D − W
-- statement:
--   Let $W=(w_{uv})\in\mathbb R^{n\times n}$ be a weight matrix with Laplacian $\Delta=D-W$, $d_u=\sum_v w_{uv}$, and let $X\in\mathbb R^{n\times d}$ have rows $x_u$. Write $\mathcal N_u=\{v: w_{uv}\ne 0\}$. Then for every node $u$,
--   $$(\Delta X)_u=\sum_{v\in\mathcal N_u} w_{uv}(x_u-x_v)= d_u x_u-\sum_{v\in\mathcal N_u} w_{uv}x_v .$$
--
--   The first identity says that the matrix form $\Delta=D-W$ of the Laplacian is the local difference operator (24); the second is the local aggregation $\phi(x_u,X_{\mathcal N_u})$ the book reads off from it. In particular row $u$ of $\Delta X$ depends only on $x_u$ and the features of the neighbours of $u$: the Laplacian is local.
--
--   **Formalization Note** The page calls $\Delta$ "an $n\times n$ symmetric matrix"; symmetry holds only for symmetric $W$ (the side-note on the same page) and is not part of this identity. It is stated separately, under $W=W^\top$, in the side-note theorem of p. 64.
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning (arXiv:2104.13478v2), §4.6, (24) and the sentence after it, p. 62

import Mathlib
import Definitions.Def_GeomDL_Filters_Defs

namespace GeomDL.Filters
open Matrix
/-- §4.6, p. 62, (24): row `u` of `ΔX` is `∑_{v∈𝒩_u} w_uv (x_u − x_v)`, and equals the local
aggregation `φ(x_u, X_{𝒩_u}) = d_u x_u − ∑_{v∈𝒩_u} w_uv x_v` with `d_u = ∑_v w_uv`.
Rows of `X ∈ ℝ^{n×d}` are the node features `x_u`. -/
theorem eq_24_lap_mul_apply {n d : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (X : Matrix (Fin n) (Fin d) ℝ)
    (u : Fin n) :
    (lap W * X) u = ∑ v ∈ nbhd W u, W u v • (X u - X v) ∧
      (lap W * X) u = (∑ v, W u v) • X u - ∑ v ∈ nbhd W u, W u v • X v := by sorry
end GeomDL.Filters
