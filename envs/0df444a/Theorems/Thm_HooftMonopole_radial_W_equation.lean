-- Prove2me | Theorems.Thm_HooftMonopole_radial_W_equation
-- name    : HooftMonopole.radial_W_equation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T20:04:12.588227+00:00
-- url     : https://prove2.me/theorems/6e43caa0-8895-4e4b-ba29-dc05fb738ea2
-- title:
--   Eq. (2.13): the Lagrange equation for the radial gauge profile $W(r)$
-- statement:
--   Let $e,\lambda,F\in\mathbb R$ and let $Q(r),W(r)$ be real functions such that the spherically symmetric configuration $Q_a(x) = x_aQ(|x|)$, $W^a_i(x) = \varepsilon_{iab}x_bW(|x|)$ is a static solution of the Georgi–Glashow field equations (smooth, of finite energy, and stationary for the energy under all smooth compactly supported variations). Then for every $r > 0$,
--   $$\frac{d}{dr}\Big(2r^4\frac{dW}{dr} + 4r^3W\Big) = r^2\Big[4r\frac{dW}{dr} + 12W + 6er^2W^2 + 2e^2r^4W^3 + 2er^2Q^2 + 2e^2r^4WQ^2\Big].$$
--
--   This is the Euler–Lagrange equation of the reduced functional (2.9) with respect to $W$, the equation used in the asymptotic analysis (2.14)–(2.15).
--
--   **Formalization Note** The hypothesis is stationarity of the full three-dimensional energy; the conclusion is the radial equation. Smoothness of the profiles on $(0,\infty)$ is not assumed separately.
-- source:
--   G. 't Hooft, Magnetic monopoles in unified gauge theories, Nucl. Phys. B79 (1974) 276-284, https://doi.org/10.1016/0550-3213(74)90486-6, p. 280, eq. (2.13) (from (2.9))

import Mathlib
import Definitions.Def_HooftMonopole_Defs

open MeasureTheory Filter Topology Real

namespace HooftMonopole

theorem radial_W_equation (e lam F : ℝ) (q w : ℝ → ℝ)
    (hsol : IsStaticSolution e lam F (hedgehogHiggs q) (hedgehogGauge w)) :
    ∀ r : ℝ, 0 < r → radialWEquation e w q r := by sorry

end HooftMonopole
