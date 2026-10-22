-- Prove2me | Theorems.Thm_GeomDL_EGNN_layer_E3_equivariant
-- name    : GeomDL.EGNN.layer_E3_equivariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T18:14:17.492729+00:00
-- url     : https://prove2.me/theorems/bdd4fb51-f2b9-4e6b-816c-4fbcaad696cc
-- title:
--   §5.5, pp. 83–84 — the Satorras et al. layer keeps node features invariant and moves coordinates with every rigid motion
-- statement:
--   Let a graph on $n$ nodes have adjacency matrix $\mathbf A$ and neighbourhoods $\mathcal N_u$. Each node $u$ carries features $\mathbf f_u\in\mathbb R^d$ and coordinates $\mathbf x_u\in\mathbb R^3$. For arbitrary functions $\phi$, $\psi_{\mathrm f}$, a real-valued $\psi_{\mathrm c}$ and an arbitrary aggregator $\bigoplus$ of multisets, the equivariant message-passing layer of Satorras et al. (2021) is
--   $$\mathbf f'_u = \phi\Big(\mathbf f_u, \bigoplus_{v\in\mathcal N_u}\psi_{\mathrm f}(\mathbf f_u,\mathbf f_v,\|\mathbf x_u-\mathbf x_v\|^2)\Big), \qquad \mathbf x'_u = \mathbf x_u + \sum_{v\neq u}(\mathbf x_u-\mathbf x_v)\,\psi_{\mathrm c}(\mathbf f_u,\mathbf f_v,\|\mathbf x_u-\mathbf x_v\|^2).$$
--   Let $\mathbf R$ be any $3\times3$ orthogonal matrix and $\mathbf b\in\mathbb R^3$. If the layer is applied to the same features and the transformed coordinates $\mathbf R\mathbf x_u+\mathbf b$, producing $(\mathbf f''_u,\mathbf x''_u)$, then for every node $u$
--   $$\mathbf f''_u = \mathbf f'_u \qquad\text{and}\qquad \mathbf x''_u = \mathbf R\mathbf x'_u+\mathbf b.$$
--
--   So the output features are E(3)-invariant and the output coordinates are E(3)-equivariant: the equivariance property the book states on p. 83, for the layer of p. 84. It is the property that makes the layer suitable for molecular graphs, whose predictions must not depend on how the molecule is placed in space.
--
--   **Formalization Note** $\mathbf R$ ranges over `Matrix.orthogonalGroup (Fin 3) ℝ` (rotations and reflections) and acts on `EuclideanSpace ℝ (Fin 3)` by `Matrix.toEuclideanLin`. The layer takes the coordinates themselves, not only their distance matrix. The feature update aggregates over $\mathcal N_u$ and the coordinate update sums over all $v\neq u$, as printed. No hypothesis is added; $n = 0$ is allowed (both sides are empty).
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §5.5, p. 83 (the equivariance property) and p. 84 (the Satorras et al. layer, "It can be shown that such an aggregation is equivariant under Euclidean transformations of the spatial coordinates")

import Mathlib
import Definitions.Def_GeomDL_EGNN_Defs

namespace GeomDL.EGNN

/-- §5.5, pp. 83–84: the Satorras et al. (2021) layer is E(3)-equivariant. If the coordinates
are transformed by `g ∈ E(3)`, `x_u ↦ Rx_u + b` with `R ∈ O(3)` and `b ∈ ℝ³`, then the output
features `f'_u` are unchanged and the output coordinates transform in the same way,
`x'_u ↦ Rx'_u + b`. -/
theorem layer_E3_equivariant {n d : ℕ} {M M' F' : Type*} (φ : (Fin d → ℝ) → M' → F')
    (agg : Multiset M → M') (ψf : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → M)
    (ψc : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (f : Matrix (Fin n) (Fin d) ℝ) (x : Fin n → E3)
    (R : Matrix.orthogonalGroup (Fin 3) ℝ) (b : E3) :
    (egnnLayer φ agg ψf ψc A f (fun u => rigid R b (x u))).1 = (egnnLayer φ agg ψf ψc A f x).1 ∧
    ∀ u, (egnnLayer φ agg ψf ψc A f (fun u => rigid R b (x u))).2 u =
      rigid R b ((egnnLayer φ agg ψf ψc A f x).2 u) := by sorry

end GeomDL.EGNN
