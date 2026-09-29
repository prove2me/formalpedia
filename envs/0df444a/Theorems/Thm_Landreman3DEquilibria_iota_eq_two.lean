-- Prove2me | Theorems.Thm_Landreman3DEquilibria_iota_eq_two
-- name    : Landreman3DEquilibria.iota_eq_two
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-23T19:26:17.468247+00:00
-- url     : https://prove2.me/theorems/7b1d9f02-fe5f-459d-b79c-fa485c9a3d1f
-- title:
--   Rotational transform $\iota=2$ on every surface
-- statement:
--   Let $0<\epsilon<1$ and $0<\delta<(1-\epsilon)^2/4$, and take a field line with labels $(u,v)$ lying on a non-degenerate surface of the plasma domain, that is with
--
--   $$0<\psi=\Big(u+\frac\epsilon2\Big)^2+v^2\le\delta .$$
--
--   Measure the poloidal angle by the geometric angle relative to the magnetic axis,
--
--   $$\theta=\arg\Big[(R-R_a)-i\big(z-Z_a(\phi)\big)\Big],\qquad R_a=\sqrt{1-\epsilon^2},\quad Z_a(\phi)=\frac{\epsilon}{2}\sin2\phi ,$$
--
--   evaluated along the field line $\zeta\mapsto r(u,v,\zeta)$. Then this angle admits a continuous determination $\theta(\zeta)$ along the line, and over one toroidal transit $\Delta\phi=2\pi$ it increases by
--
--   $$\Delta\theta=4\pi,\qquad\text{so}\qquad \iota=\frac{\Delta\theta}{\Delta\phi}=2 .$$
--
--   The rotational transform therefore takes the same integer value $2$ on every flux surface of the configuration: the field lines all close after a single toroidal circuit, and the transform profile is uniform rather than sheared.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, eqs. (2.23) and (2.25); Section 2.4

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem iota_eq_two (e d u v : ℝ) (he : 0 < e) (he1 : e < 1) (hd : 0 < d)
    (hd' : d < (1 - e) ^ 2 / 4) (hpos : 0 < (u + e / 2) ^ 2 + v ^ 2)
    (hle : (u + e / 2) ^ 2 + v ^ 2 ≤ d) :
    ∃ theta : ℝ → ℝ, Continuous theta ∧
      (∀ z : ℝ, poloidalDisp e (posMap e u v z) =
        (‖poloidalDisp e (posMap e u v z)‖ : ℂ) * Complex.exp (theta z * Complex.I)) ∧
      theta (2 * Real.pi) - theta 0 = 4 * Real.pi := by sorry

end Landreman3DEquilibria
