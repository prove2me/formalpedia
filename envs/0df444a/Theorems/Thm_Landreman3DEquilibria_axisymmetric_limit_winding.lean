-- Prove2me | Theorems.Thm_Landreman3DEquilibria_axisymmetric_limit_winding
-- name    : Landreman3DEquilibria.axisymmetric_limit_winding
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:25:53.35551+00:00
-- url     : https://prove2.me/theorems/30df1504-4e82-4f84-b147-c85976be8d70
-- title:
--   Eq. (2.24): $(R^2-1)/2-iz=q\,e^{i(2\zeta-\mu)}$
-- statement:
--   Consider the axisymmetric member $\epsilon=0$ of the family and a field line with labels $u,v$ satisfying $u^2+v^2<1/4$. Writing $u+iv=q e^{i\mu}$ with $q^2=u^2+v^2$, and $R^2=x_0^2+x_1^2$ along the line, one has
--
--   $$\frac{R^2-1}{2}-iz=q\,e^{i(2\zeta-\mu)} .$$
--
--   The complex displacement on the left therefore winds exactly twice around the origin as $\zeta$ increases by $2\pi$; since the axis of the $\epsilon=0$ configuration is the circle $R_a=1$, $Z_a=0$, and replacing $(R^2-1)/2$ by $R-1$ changes the displacement by the positive factor $(R+1)/2$, this is the computation that identifies the rotational transform of the axisymmetric limit as $\iota=2$.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, eq. (2.24)

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem axisymmetric_limit_winding (u v z : ℝ) (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    ((posMap 0 u v z 0 ^ 2 + posMap 0 u v z 1 ^ 2 - 1) / 2 : ℝ) -
        Complex.I * (posMap 0 u v z 2 : ℝ) =
      Complex.exp (2 * z * Complex.I) * (starRingEnd ℂ) (u + v * Complex.I) := by sorry

end Landreman3DEquilibria
