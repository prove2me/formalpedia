-- Prove2me | Theorems.Thm_GeomDL_Filters_eq_24_perm_equivariant
-- name    : GeomDL.Filters.eq_24_perm_equivariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T18:14:12.982978+00:00
-- url     : https://prove2.me/theorems/3aaa7a73-2387-499a-b4ad-e37de83fa026
-- title:
--   §4.6, p. 62 — F(X) = ΔX is permutation equivariant: Δ(PWPᵀ)(PX) = P(Δ(W)X)
-- statement:
--   Let $W\in\mathbb R^{n\times n}$ be a weight matrix with Laplacian $\Delta(W)=D-W$ as in (24), let $X\in\mathbb R^{n\times d}$, and let $P$ be the permutation matrix of a permutation $\sigma$ of the nodes, acting by $(PX)_u=x_{\sigma^{-1}(u)}$. Relabelling the nodes moves both the features and the weights, $X\mapsto PX$ and $W\mapsto PWP^\top$, and
--   $$\Delta(PWP^\top)\,(PX)=P\,\big(\Delta(W)X\big).$$
--
--   This is the statement that $F(X)=\Delta X$ is an instance of the book's permutation-equivariant blueprint (13) on graphs: the layer computes the same thing whatever order the nodes are listed in.
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning (arXiv:2104.13478v2), §4.6, p. 62, "F(X) = ∆X is in fact an instance of our general blueprint (13)"

import Mathlib
import Definitions.Def_GeomDL_Filters_Defs

namespace GeomDL.Filters
open Matrix
/-- §4.6, p. 62: `F(X) = ΔX` with `Δ` from (24) is permutation equivariant in the sense of the
blueprint (13): relabelling the nodes by `σ` (`X ↦ PX`, `W ↦ PWPᵀ`) relabels the output,
`Δ(PWPᵀ) (PX) = P (Δ(W) X)`. -/
theorem eq_24_perm_equivariant {n d : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (X : Matrix (Fin n) (Fin d) ℝ) (σ : Equiv.Perm (Fin n)) :
    lap (GeomDL.Sets.permAdj σ W) * GeomDL.Sets.permRows σ X = GeomDL.Sets.permRows σ (lap W * X) := by sorry
end GeomDL.Filters
