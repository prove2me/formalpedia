-- Prove2me | Theorems.Thm_HooftMonopole_hedgehog_energyDensity
-- name    : HooftMonopole.hedgehog_energyDensity
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-23T20:03:25.173935+00:00
-- url     : https://prove2.me/theorems/896eb469-ad24-4bc5-a807-4db434bd4549
-- title:
--   Eq. (2.9): energy density of the spherically symmetric ansatz
-- statement:
--   Let $e,\lambda,F\in\mathbb R$ and let $Q(r), W(r)$ be real functions. Consider the spherically symmetric configuration (2.8)
--   $$Q_a(x) = x_a\,Q(|x|),\qquad W^a_i(x) = \varepsilon_{iab}\,x_b\,W(|x|).$$
--   Let $x \neq 0$, $r = |x|$, and assume $Q$ and $W$ are differentiable at $r$. Then the static energy density $\mathcal E = \frac14G^a_{ij}G^a_{ij} + \frac12D_iQ_aD_iQ_a + \frac18\lambda(Q_aQ_a - F^2)^2$ of this configuration at $x$ equals
--   $$r^2W'^2 + 4rWW' + 6W^2 + 2er^2W^3 + \tfrac12e^2r^4W^4 + \tfrac12r^2Q'^2 + rQQ' + \tfrac32Q^2 + 2er^2WQ^2 + e^2r^4W^2Q^2 - \tfrac14\lambda F^2r^2Q^2 + \tfrac18\lambda r^4Q^4 + \tfrac18\lambda F^4,$$
--   with all profiles evaluated at $r$. This is minus the bracket of eq. (2.9).
--
--   This identity reduces the three-dimensional energy of the ansatz to a one-dimensional functional; it is the input for the Lagrange equation (2.13) and for the dimensionless form (3.2).
--
--   **Formalization Note** No sign conditions on $e,\lambda,F$ are needed. Differentiability of the profiles at $|x|$ is assumed so that the Fréchet derivatives of the fields are the ones computed from $Q'$ and $W'$.
-- source:
--   G. 't Hooft, Magnetic monopoles in unified gauge theories, Nucl. Phys. B79 (1974) 276-284, https://doi.org/10.1016/0550-3213(74)90486-6, p. 280, eqs. (2.8)-(2.9) (Lagrangian (2.1)-(2.3))

import Mathlib
import Definitions.Def_HooftMonopole_Defs

open MeasureTheory Filter Topology Real

namespace HooftMonopole

theorem hedgehog_energyDensity (e lam F : ℝ) (q w : ℝ → ℝ) (x : Space) (hx : x ≠ 0)
    (hq : DifferentiableAt ℝ q ‖x‖) (hw : DifferentiableAt ℝ w ‖x‖) :
    energyDensity e lam F (hedgehogHiggs q) (hedgehogGauge w) x =
      radialEnergyIntegrand e lam F w q ‖x‖ := by sorry

end HooftMonopole
