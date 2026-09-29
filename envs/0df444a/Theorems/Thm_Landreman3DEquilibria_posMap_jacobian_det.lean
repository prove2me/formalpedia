-- Prove2me | Theorems.Thm_Landreman3DEquilibria_posMap_jacobian_det
-- name    : Landreman3DEquilibria.posMap_jacobian_det
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:07:45.213894+00:00
-- url     : https://prove2.me/theorems/39f22c2d-0db7-4dd6-bcf5-2bd000d01f79
-- title:
--   $\det\,\partial(x,y,z)/\partial(u,v,\zeta)=-ab$
-- statement:
--   Let $0<\epsilon<1$ and $u^2+v^2<1/4$, and let $r(u,v,\zeta)$ be the field-line position map. Then the Jacobian determinant of the change of variables from $(u,v,\zeta)$ to Cartesian coordinates is the constant
--
--   $$\det\frac{\partial(x,y,z)}{\partial(u,v,\zeta)}=-ab,\qquad a=\sqrt{1+\epsilon},\ b=\sqrt{1-\epsilon}.$$
--
--   Since $-ab\neq0$, the map is locally invertible; the constancy of the Jacobian is what makes the volume and volume-average computations in the source elementary.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, eq. (2.13)

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem posMap_jacobian_det (e u v z : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    (Matrix.of
      ![![deriv (fun t => posMap e t v z 0) u, deriv (fun t => posMap e u t z 0) v,
          deriv (fun t => posMap e u v t 0) z],
        ![deriv (fun t => posMap e t v z 1) u, deriv (fun t => posMap e u t z 1) v,
          deriv (fun t => posMap e u v t 1) z],
        ![deriv (fun t => posMap e t v z 2) u, deriv (fun t => posMap e u t z 2) v,
          deriv (fun t => posMap e u v t 2) z]]).det = -(aCoef e * bCoef e) := by sorry

end Landreman3DEquilibria
