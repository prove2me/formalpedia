-- Prove2me | Theorems.Thm_GeomDL_Cotangent_edge_length_triangle_inequality
-- name    : GeomDL.Cotangent.edge_length_triangle_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:39.674793+00:00
-- url     : https://prove2.me/theorems/35b518b0-60a1-47a4-96aa-65def5c41662
-- title:
--   §4.6, p. 61 — the mesh metric ℓ_uv = ‖x_u − x_v‖ satisfies the triangle inequality on every face
-- statement:
--   Let $\mathcal F$ be the faces of a manifold triangular mesh whose nodes are embedded by $\mathbf x_1,\dots,\mathbf x_n$ in a Euclidean space, and let $\ell_{uv} = \|\mathbf x_u - \mathbf x_v\|$ be the induced metric. For every face $(u,v,q) \in \mathcal F$, every combination of its edges satisfies the triangle inequality:
--   $$\ell_{uv} \le \ell_{uq} + \ell_{vq}, \qquad \ell_{uq} \le \ell_{uv} + \ell_{qv}, \qquad \ell_{vq} \le \ell_{vu} + \ell_{qu}.$$
--
--   This is what makes $\ell$ a metric on the mesh, so that a property expressed solely in terms of $\ell$ is called intrinsic.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.6, p. 61, "A metric defined in this way automatically satisfies properties such as the triangle inequality"

import Mathlib
import Definitions.Def_GeomDL_Cotangent_Defs

open EuclideanGeometry

namespace GeomDL.Cotangent

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- §4.6, p. 61: the metric `ℓ_uv = ‖x_u − x_v‖` induced by the embedding satisfies the
    triangle inequality on every face `(u, v, q) ∈ F` of a manifold mesh, for every
    combination of its edges. -/
    theorem edge_length_triangle_inequality {n : ℕ} (M : TriMesh n) (x : Fin n → P)
        (hmesh : IsManifoldMesh M) {u v q : Fin n} (hF : (u, v, q) ∈ M.faces) :
    edgeLength x u v ≤ edgeLength x u q + edgeLength x v q ∧
    edgeLength x u q ≤ edgeLength x u v + edgeLength x q v ∧
    edgeLength x v q ≤ edgeLength x v u + edgeLength x q u := by sorry

end GeomDL.Cotangent
