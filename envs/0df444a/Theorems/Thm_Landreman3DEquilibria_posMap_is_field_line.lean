-- Prove2me | Theorems.Thm_Landreman3DEquilibria_posMap_is_field_line
-- name    : Landreman3DEquilibria.posMap_is_field_line
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:06:45.018993+00:00
-- url     : https://prove2.me/theorems/a2f8660c-a672-4872-a96b-7429016e2fc6
-- title:
--   The position map $r(u,v,\zeta)$ integrates $B$
-- statement:
--   Let $0<\epsilon<1$ and let $u,v$ satisfy $u^2+v^2<1/4$. Put $q^2=u^2+v^2$ and
--
--   $$L=\left(\frac{1+\sqrt{1-4q^2}}{2}\right)^{1/2},\qquad\text{so that}\qquad L^2+\frac{q^2}{L^2}=1 ,$$
--
--   and let
--
--   $$r(u,v,\zeta)=\Big(a\big[L\cos\zeta+\tfrac{u\cos\zeta+v\sin\zeta}{L}\big],\ b\big[L\sin\zeta+\tfrac{v\cos\zeta-u\sin\zeta}{L}\big],\ v\cos2\zeta-u\sin2\zeta\Big).$$
--
--   Then for every $\zeta$,
--
--   $$\frac{\partial r}{\partial\zeta}(u,v,\zeta)=B\big(r(u,v,\zeta)\big),$$
--
--   so the curves $\zeta\mapsto r(u,v,\zeta)$ are exactly the integral curves of the magnetic field, with $(u,v)$ labelling the field line and $\zeta$ playing the role of a toroidal angle of period $2\pi$.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, eqs. (2.10)-(2.12): 'Direct substitution confirms B(r) = ∂ζ r'

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem posMap_is_field_line (e u v z : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) (i : Fin 3) :
    deriv (fun t => posMap e u v t i) z = Bfield e (posMap e u v z) i := by sorry

end Landreman3DEquilibria
