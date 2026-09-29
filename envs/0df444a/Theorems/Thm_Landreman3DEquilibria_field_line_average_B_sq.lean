-- Prove2me | Theorems.Thm_Landreman3DEquilibria_field_line_average_B_sq
-- name    : Landreman3DEquilibria.field_line_average_B_sq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:33:03.964272+00:00
-- url     : https://prove2.me/theorems/150e6e84-40c6-4e15-b871-126ed49b3ae5
-- title:
--   Eq. (2.26): field-line average of $|B|^2$
-- statement:
--   Let $0<\epsilon<1$ and $u^2+v^2<1/4$. Averaging the squared field strength over one toroidal period of the field line labelled $(u,v)$ gives, with $\psi=(u+\epsilon/2)^2+v^2$,
--
--   $$\frac{1}{2\pi}\int_0^{2\pi}\big|B\big(r(u,v,\zeta)\big)\big|^2\,d\zeta=1-\frac{\epsilon^2}{2}+2\psi .$$
--
--   The average depends on the field line only through its flux label. Combined with $\langle\psi\rangle_V=\delta/2$, which follows from the proportionality of volume to $\psi$, this yields the volume-averaged field strength and hence the volume-averaged beta of the configuration.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, eq. (2.26)

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem field_line_average_B_sq (e u v : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    (1 / (2 * Real.pi)) * ∫ z in (0 : ℝ)..(2 * Real.pi), normSq (Bfield e (posMap e u v z)) =
      1 - e ^ 2 / 2 + 2 * ((u + e / 2) ^ 2 + v ^ 2) := by sorry

end Landreman3DEquilibria
