-- Prove2me | Theorems.Thm_Larmor_sphere_integral_transverse
-- name    : Larmor.sphere_integral_transverse
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T01:21:26.991013+00:00
-- url     : https://prove2.me/theorems/88a8506a-28ec-4602-b92e-d8258779956c
-- title:
--   $\int_{\|x\|=R}\bigl(\|a\|^2-\langle a,x/R\rangle^2\bigr)\,\mathrm d\mathcal H^2=\tfrac{8\pi}{3}R^2\|a\|^2$
-- statement:
--   **The angular integral behind Larmor's factor $6\pi$.** Let $R>0$ and let $a\in\mathbb{R}^3$ be arbitrary. Then
--
--   $$\int_{\|x\|=R}\Bigl(\|a\|^{2}-\bigl\langle a,\tfrac{x}{R}\bigr\rangle^{2}\Bigr)\,\mathrm d\mathcal H^{2}(x)=\frac{8\pi}{3}\,R^{2}\,\|a\|^{2},$$
--
--   the integral being taken against two-dimensional Hausdorff measure on the sphere of radius $R$, which is its surface-area measure.
--
--   Writing $n=x/R$ and letting $\theta$ be the angle between $a$ and $n$, the integrand is $\|a\|^2\sin^2\theta$, so the identity is the classical $\int\sin^2\theta\,\mathrm d\Omega=8\pi/3$: the total surface area $4\pi R^2$ minus the contribution $\int\langle a,n\rangle^2=\frac{4\pi}{3}R^2\|a\|^2$ coming from the longitudinal component. It is this factor that converts the $\sin^2\theta$ angular distribution of dipole radiation into the coefficient $1/(6\pi)$ of the Larmor formula, and it is reusable in any multipole or antenna computation.
-- source:
--   https://en.wikipedia.org/wiki/Larmor_formula — Derivation section, where the surface integral of the Poynting vector over a sphere produces the factor $8\pi/3$; J. D. Jackson, Classical Electrodynamics, 3rd ed., Wiley 1998, §14.2.

import Definitions.Def_Larmor_vec3

open MeasureTheory

namespace Larmor

theorem sphere_integral_transverse (R : ℝ) (hR : 0 < R) (a : Vec) :
    ∫ x in Metric.sphere (0 : Vec) R, (‖a‖ ^ 2 - (inner ℝ a (R⁻¹ • x) : ℝ) ^ 2) ∂(μH[2])
      = 8 * Real.pi / 3 * R ^ 2 * ‖a‖ ^ 2 := by sorry

end Larmor
