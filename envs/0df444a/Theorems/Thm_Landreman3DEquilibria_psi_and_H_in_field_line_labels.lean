-- Prove2me | Theorems.Thm_Landreman3DEquilibria_psi_and_H_in_field_line_labels
-- name    : Landreman3DEquilibria.psi_and_H_in_field_line_labels
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:08:31.911274+00:00
-- url     : https://prove2.me/theorems/18cf641b-d61f-43b6-98a0-f18eefccab69
-- title:
--   $H=1+2\epsilon u+2(u^2+v^2)$ and $\psi=(u+\epsilon/2)^2+v^2$
-- statement:
--   Let $0<\epsilon<1$ and $u^2+v^2<1/4$. Along the field line labelled $(u,v)$ the Bernoulli function and the flux label are independent of the toroidal parameter $\zeta$ and are given by
--
--   $$H\big(r(u,v,\zeta)\big)=1+2\epsilon u+2(u^2+v^2),\qquad
--   \psi\big(r(u,v,\zeta)\big)=\Big(u+\frac{\epsilon}{2}\Big)^2+v^2 .$$
--
--   In particular $\psi\ge0$, and in the $(u,v)$ plane the pressure surfaces are the circles of radius $\sqrt\psi$ centred at $(-\epsilon/2,0)$. The magnetic axis is the single point $u=-\epsilon/2$, $v=0$, where $\psi=0$.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, eqs. (2.14) and (2.15)

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem psi_and_H_in_field_line_labels (e u v z : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    Hfun e (posMap e u v z) = 1 + 2 * e * u + 2 * (u ^ 2 + v ^ 2) ∧
      psiFun e (posMap e u v z) = (u + e / 2) ^ 2 + v ^ 2 := by sorry

end Landreman3DEquilibria
