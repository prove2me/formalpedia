-- Prove2me | Theorems.Thm_Landreman3DEquilibria_psi_in_field_line_labels
-- name    : Landreman3DEquilibria.psi_in_field_line_labels
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T19:17:39.126149+00:00
-- url     : https://prove2.me/theorems/d1d2e99d-c3a5-4add-9677-d5324522c1a2
-- title:
--   $\psi=(u+\epsilon/2)^2+v^2$ along field lines
-- statement:
--   Let $0<\epsilon<1$ and $u^2+v^2<1/4$. Along the field line labelled $(u,v)$, the flux label $\psi = \frac{1}{2}(H - 1 + \epsilon^2/2)$ is independent of the toroidal parameter $\zeta$ and is given by:
--
--   $$ \psi\big(r(u,v,\zeta)\big) = \Big(u + \frac{\epsilon}{2}\Big)^2 + v^2. $$
--
--   In particular, the magnetic flux surfaces in the $(u,v)$ plane are concentric circles of radius $\sqrt{\psi}$ centered at $(-\epsilon/2, 0)$, with the magnetic axis located at the minimum $u = -\epsilon/2, v = 0$ where $\psi = 0$. This is eq. (2.15) of Landreman (2026).
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), Section 2, eq. (2.15)

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem psi_in_field_line_labels (e u v z : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    psiFun e (posMap e u v z) = (u + e / 2) ^ 2 + v ^ 2 := by sorry

end Landreman3DEquilibria
