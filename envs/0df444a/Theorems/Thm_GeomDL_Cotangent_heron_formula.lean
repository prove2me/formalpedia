-- Prove2me | Theorems.Thm_GeomDL_Cotangent_heron_formula
-- name    : GeomDL.Cotangent.heron_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:45.791977+00:00
-- url     : https://prove2.me/theorems/b7c59090-500f-4f94-b562-1beb3d9854fa
-- title:
--   §4.6, p. 63 — Heron's formula: a_uvq = √(s(s − ℓ_uv)(s − ℓ_vq)(s − ℓ_uq)) with s = ½(ℓ_uv + ℓ_uq + ℓ_vq)
-- statement:
--   Let $\mathbf x_u, \mathbf x_v, \mathbf x_q$ be three points of a Euclidean space, with side lengths $\ell_{uv}, \ell_{vq}, \ell_{uq}$, and let $a_{uvq} = \frac12 \ell_{uq}\ell_{vq}\sin\angle uqv$ be the area of the triangle they span. With the semiperimeter $s_{uvq} = \frac12(\ell_{uv} + \ell_{uq} + \ell_{vq})$,
--   $$a_{uvq} = \sqrt{s_{uvq}(s_{uvq} - \ell_{uv})(s_{uvq} - \ell_{vq})(s_{uvq} - \ell_{uq})}.$$
--   The identity holds for every triple of points; for a degenerate triangle both sides are $0$.
--
--   Heron's formula expresses the area of each face through the metric $\ell$ alone, which is one half of the intrinsic description of the cotangent weights.
--
--   **Formalization Note** The left-hand side is the geometric area $\frac12\ell_{uq}\ell_{vq}\sin\angle uqv$, so the formula is a theorem, not a definition. Mathlib has Heron's formula only in its `Archive`, which cannot be imported.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.6, p. 63, "where the area of the triangles a_ijk is given as … using Heron's semiperimeter formula"

import Mathlib
import Definitions.Def_GeomDL_Cotangent_Defs

open EuclideanGeometry

namespace GeomDL.Cotangent

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- §4.6, p. 63, Heron's formula: the area `a_uvq = ½ ℓ_uq ℓ_vq sin ∠uqv` of the triangle
`(u, v, q)` equals `√(s(s − ℓ_uv)(s − ℓ_vq)(s − ℓ_uq))` with `s = ½(ℓ_uv + ℓ_uq + ℓ_vq)`.
Holds for every triple of nodes (degenerate triangles: both sides are `0`). -/
theorem heron_formula {ι : Type*} (x : ι → P) (u v q : ι) :
    triArea (x u) (x v) (x q) =
      heron (edgeLength x u v) (edgeLength x v q) (edgeLength x u q) := by sorry

end GeomDL.Cotangent
