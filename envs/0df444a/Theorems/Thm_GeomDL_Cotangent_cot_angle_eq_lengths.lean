-- Prove2me | Theorems.Thm_GeomDL_Cotangent_cot_angle_eq_lengths
-- name    : GeomDL.Cotangent.cot_angle_eq_lengths
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:44.828868+00:00
-- url     : https://prove2.me/theorems/10856ea7-14bd-41b8-b403-e0a6ee4ef5ea
-- title:
--   §4.6, p. 63 — one face's term of the intrinsic cotangent weight equals ½ cot ∠uqv
-- statement:
--   Let $\mathbf x_u, \mathbf x_v, \mathbf x_q$ be the vertices of a non-degenerate triangle (not collinear) in a Euclidean space, with side lengths $\ell_{uv}, \ell_{vq}, \ell_{uq}$ and area $a_{uvq} = \frac12\ell_{uq}\ell_{vq}\sin\angle uqv$. The cotangent of the angle $\angle uqv$ at $\mathbf x_q$, opposite the edge $(u,v)$, is
--   $$\cot\angle uqv = \frac{-\ell_{uv}^2 + \ell_{vq}^2 + \ell_{uq}^2}{4\,a_{uvq}}.$$
--   Equivalently, the term $\dfrac{-\ell_{uv}^2 + \ell_{vq}^2 + \ell_{uq}^2}{8\,a_{uvq}}$ contributed by the face $(u,q,v)$ to the intrinsic expression of the cotangent weight is $\frac12\cot\angle uqv$.
--
--   Combined with Heron's formula, this writes the cotangent of every angle of the mesh in terms of edge lengths only.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.6, p. 63, display for w_uv (first summand)

import Mathlib
import Definitions.Def_GeomDL_Cotangent_Defs

open EuclideanGeometry

namespace GeomDL.Cotangent

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- §4.6, p. 63: for a non-degenerate triangle `(u, v, q)`, the cotangent of the angle `∠uqv`
at `q` (opposite the edge `(u, v)`) is `(−ℓ²_uv + ℓ²_vq + ℓ²_uq) / (4 a_uvq)`, so one face's
term `(−ℓ²_uv + ℓ²_vq + ℓ²_uq) / (8 a_uvq)` of the intrinsic display is `½ cot ∠uqv`. -/
theorem cot_angle_eq_lengths {ι : Type*} (x : ι → P) {u v q : ι}
    (hnd : AffineIndependent ℝ ![x u, x v, x q]) :
    Real.cot (∠ (x u) (x q) (x v)) =
      (-(edgeLength x u v) ^ 2 + (edgeLength x v q) ^ 2 + (edgeLength x u q) ^ 2) /
        (4 * triArea (x u) (x v) (x q)) := by sorry

end GeomDL.Cotangent
