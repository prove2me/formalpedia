-- Prove2me | Theorems.Thm_Landreman3DEquilibria_H_at_toroidal_zero
-- name    : Landreman3DEquilibria.H_at_toroidal_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T19:24:54.193589+00:00
-- url     : https://prove2.me/theorems/58bdd04a-f8cf-4c5b-b8cd-939519f488cc
-- title:
--   $H(r(u,v,0)) = 1 + 2\epsilon u + 2(u^2 + v^2)$ at $\zeta=0$
-- statement:
--   Let $0<\epsilon<1$ and $u^2+v^2<1/4$. At the toroidal cross-section $\zeta = 0$, evaluating the Bernoulli function $H = Q + \frac{1}{2}|B|^2$ on the field-line position $r(u,v,0)$ yields:
--
--   $$ H\big(r(u,v,0)\big) = 1 + 2\epsilon u + 2(u^2 + v^2). $$
--
--   At $\zeta = 0$, all trigonometric dependence on $\zeta$ disappears, and the formula simplifies algebraically to the quadratic profile in field-line labels.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), Section 2, eq. (2.14)

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem H_at_toroidal_zero (e u v : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    Hfun e (posMap e u v 0) = 1 + 2 * e * u + 2 * (u ^ 2 + v ^ 2) := by sorry

end Landreman3DEquilibria
