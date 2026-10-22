-- Prove2me | Theorems.Thm_GeomDL_Cotangent_isometry_invariance
-- name    : GeomDL.Cotangent.isometry_invariance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:52.804438+00:00
-- url     : https://prove2.me/theorems/c89885df-e52e-4778-9d6a-fff3ec90b581
-- title:
--   §4.6, p. 63 — isometry invariance: a deformation of the mesh preserving ℓ does not change the cotangent Laplacian
-- statement:
--   Let $\mathcal F$ be the faces of a manifold triangular mesh on the nodes $1,\dots,n$, and let $\mathbf x$ and $\mathbf x'$ be two embeddings of the nodes in a Euclidean space that induce the same metric on the mesh: for every face $(u,v,q)\in\mathcal F$,
--   $$\|\mathbf x_u - \mathbf x_v\| = \|\mathbf x'_u - \mathbf x'_v\|,\quad \|\mathbf x_v - \mathbf x_q\| = \|\mathbf x'_v - \mathbf x'_q\|,\quad \|\mathbf x_u - \mathbf x_q\| = \|\mathbf x'_u - \mathbf x'_q\|.$$
--   Then the cotangent Laplacians $\boldsymbol\Delta = \mathbf D - \mathbf W$ of (24) with the weights (25), computed from $\mathbf x$ and from $\mathbf x'$, are equal.
--
--   Hence everything computed from the Laplacian, such as its eigenvalues and eigenvectors, is unchanged by a deformation that does not stretch or squeeze the edges.
--
--   **Formalization Note** No non-degeneracy hypothesis is needed: the angles and areas of every face are determined by its three side lengths, including the junk values Lean assigns to degenerate triangles.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.6, p. 63, "any deformation of the mesh that does not affect the metric ℓ … does not change the Laplacian"

import Mathlib
import Definitions.Def_GeomDL_Cotangent_Defs

open EuclideanGeometry

namespace GeomDL.Cotangent

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- §4.6, p. 63, isometry invariance: two embeddings `x, x'` of the same mesh that give every
    edge of every face the same length `ℓ` have the same cotangent Laplacian (24)–(25),
    under the section's manifold-mesh assumption. -/
    theorem isometry_invariance {n : ℕ} (M : TriMesh n) (x x' : Fin n → P)
        (hmesh : IsManifoldMesh M) (hℓ : ∀ t ∈ M.faces,
      edgeLength x t.1 t.2.1 = edgeLength x' t.1 t.2.1 ∧
      edgeLength x t.2.1 t.2.2 = edgeLength x' t.2.1 t.2.2 ∧
      edgeLength x t.1 t.2.2 = edgeLength x' t.1 t.2.2) :
    cotLaplacian M x = cotLaplacian M x' := by sorry

end GeomDL.Cotangent
