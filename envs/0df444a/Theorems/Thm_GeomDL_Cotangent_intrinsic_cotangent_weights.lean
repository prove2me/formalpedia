-- Prove2me | Theorems.Thm_GeomDL_Cotangent_intrinsic_cotangent_weights
-- name    : GeomDL.Cotangent.intrinsic_cotangent_weights
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:43.422987+00:00
-- url     : https://prove2.me/theorems/834900e3-1918-4f62-897d-623f6fbaecfa
-- title:
--   §4.6, p. 63 — the cotangent weights are intrinsic: (cot ∠uqv + cot ∠upv)/2 = Σ (−ℓ²_uv + ℓ²_vq + ℓ²_uq)/(8 a_uvq), Heron areas
-- statement:
--   Let $\mathcal F$ be the faces of a manifold triangular mesh on the nodes $1,\dots,n$, embedded by points $\mathbf x_1,\dots,\mathbf x_n$ of a Euclidean space, with metric $\ell_{uv} = \|\mathbf x_u - \mathbf x_v\|$. Let $(u,v)$ be an interior edge shared by exactly two faces, $(u,q,v)$ and $(u,p,v)$, both non-degenerate triangles. Write
--   $$a_{uvq} = \sqrt{s_{uvq}(s_{uvq}-\ell_{uv})(s_{uvq}-\ell_{vq})(s_{uvq}-\ell_{uq})}, \qquad s_{uvq} = \tfrac12(\ell_{uv}+\ell_{uq}+\ell_{vq}),$$
--   for Heron's area (and likewise $a_{uvp}$). Then
--   $$\frac{\cot\angle uqv + \cot\angle upv}{2} = \frac{-\ell_{uv}^2 + \ell_{vq}^2 + \ell_{uq}^2}{8\,a_{uvq}} + \frac{-\ell_{uv}^2 + \ell_{vp}^2 + \ell_{up}^2}{8\,a_{uvp}},$$
--   and the cotangent weight (25), $w_{uv} = (\cot\angle uqv + \cot\angle upv)/(2a_u)$ with $a_u = \frac13\sum_{f\ni u} a_f$, equals the right-hand side divided by $a_u$.
--
--   The right-hand side involves only the edge lengths $\ell$, so the cotangent weights, defined in (25) through angles, depend only on the metric of the mesh: they are intrinsic.
--
--   **Formalization Note** The printed display reads $w_{uv} = \dots$ with exactly this right-hand side. The right-hand side equals $(\cot\angle uqv + \cot\angle upv)/2$, which is $a_u w_{uv}$ for the $w_{uv}$ of (25): the display omits (25)'s factor $1/a_u$. The theorem states both readings: the identity for $(\cot\angle uqv+\cot\angle upv)/2$, and $w_{uv}$ of (25) as the right-hand side over $a_u$. Here $a_u$ is computed from the geometric face areas; Heron's formula (a separate milestone) makes it intrinsic as well. Non-degeneracy of the two faces is required because Lean's $\cot$ is $0$ at the angles $0$ and $\pi$ and the Heron area of a degenerate triangle is $0$.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.6, p. 63, display "w_uv = (−ℓ²_uv + ℓ²_vq + ℓ²_uq)/(8a_uvq) + (−ℓ²_uv + ℓ²_vp + ℓ²_up)/(8a_uvp)" with Heron's formula; (25) p. 62

import Mathlib
import Definitions.Def_GeomDL_Cotangent_Defs

open EuclideanGeometry

namespace GeomDL.Cotangent

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- §4.6, p. 63 (corrected normalisation): for an interior edge `(u, v)` shared by the
    non-degenerate faces `(u, q, v)` and `(u, p, v)` of a manifold mesh,
`(cot ∠uqv + cot ∠upv)/2 = (−ℓ²_uv + ℓ²_vq + ℓ²_uq)/(8 a_uvq) + (−ℓ²_uv + ℓ²_vp + ℓ²_up)/(8 a_uvp)`
with the areas given by Heron's formula in the lengths `ℓ`, and the weight `w_uv` of (25)
is that right-hand side divided by `a_u`. The printed display omits (25)'s `1/a_u`. -/
    theorem intrinsic_cotangent_weights {n : ℕ} (M : TriMesh n) (x : Fin n → P) {u v q p : Fin n}
        (hmesh : IsManifoldMesh M) (hedge : IsInteriorEdge M u v q p)
    (hq : AffineIndependent ℝ ![x u, x v, x q]) (hp : AffineIndependent ℝ ![x u, x v, x p]) :
    (Real.cot (∠ (x u) (x q) (x v)) + Real.cot (∠ (x u) (x p) (x v))) / 2 =
        (-(edgeLength x u v) ^ 2 + (edgeLength x v q) ^ 2 + (edgeLength x u q) ^ 2) /
            (8 * heron (edgeLength x u v) (edgeLength x v q) (edgeLength x u q)) +
          (-(edgeLength x u v) ^ 2 + (edgeLength x v p) ^ 2 + (edgeLength x u p) ^ 2) /
            (8 * heron (edgeLength x u v) (edgeLength x v p) (edgeLength x u p)) ∧
      cotWeight M x u v =
        ((-(edgeLength x u v) ^ 2 + (edgeLength x v q) ^ 2 + (edgeLength x u q) ^ 2) /
            (8 * heron (edgeLength x u v) (edgeLength x v q) (edgeLength x u q)) +
          (-(edgeLength x u v) ^ 2 + (edgeLength x v p) ^ 2 + (edgeLength x u p) ^ 2) /
            (8 * heron (edgeLength x u v) (edgeLength x v p) (edgeLength x u p))) /
          vertexArea M x u := by sorry

end GeomDL.Cotangent
