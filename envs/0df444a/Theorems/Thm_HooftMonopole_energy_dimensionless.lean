-- Prove2me | Theorems.Thm_HooftMonopole_energy_dimensionless
-- name    : HooftMonopole.energy_dimensionless
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-23T20:14:45.213301+00:00
-- url     : https://prove2.me/theorems/8d45ba81-fbee-4998-907e-f8fe98700990
-- title:
--   Eq. (3.2): the monopole energy in dimensionless variables
-- statement:
--   Let $e > 0$, $F > 0$, $\lambda\in\mathbb R$, and let $Q(r), W(r)$ be real functions differentiable on $(0,\infty)$. Let $E$ be the static energy of the spherically symmetric configuration $Q_a = x_aQ(|x|)$, $W^a_i = \varepsilon_{iab}x_bW(|x|)$. Define the dimensionless profiles and parameter (3.1)
--   $$w(s) = \frac{W(s/eF)}{F^2e},\qquad q(s) = \frac{Q(s/eF)}{F^2e},\qquad \beta = \frac{\lambda}{e^2},\qquad M_W = eF .$$
--   Then
--   $$E = \frac{4\pi M_W}{e^2}\int_0^\infty s^2\Big[s^2w'^2 + 4sww' + 6w^2 + 2s^2w^3 + \tfrac12s^4w^4 + \tfrac12s^2q'^2 + sqq' + \tfrac32q^2 + 2s^2wq^2 + s^4w^2q^2 - \tfrac14\beta s^2q^2 + \tfrac18\beta s^4q^4 + \tfrac18\beta\Big]ds .$$
--
--   The bracket is dimensionless, so the monopole mass has the form $M_m = \frac{4\pi}{e^2}M_WC(\beta)$ of eq. (3.3).
--
--   **Formalization Note** Both sides are Lebesgue (Bochner) integrals; when the integrands are not integrable both sides are $0$ by convention. The bracket is the radial integrand of (2.9) with $e = F = 1$ and $\lambda = \beta$.
-- source:
--   G. 't Hooft, Magnetic monopoles in unified gauge theories, Nucl. Phys. B79 (1974) 276-284, https://doi.org/10.1016/0550-3213(74)90486-6, p. 282, eqs. (3.1)-(3.2) (with (2.9)-(2.10))

import Mathlib
import Definitions.Def_HooftMonopole_Defs

open MeasureTheory Filter Topology Real

namespace HooftMonopole

theorem energy_dimensionless (e lam F : ℝ) (he : 0 < e) (hF : 0 < F) (q w : ℝ → ℝ)
    (hq : DifferentiableOn ℝ q (Set.Ioi 0)) (hw : DifferentiableOn ℝ w (Set.Ioi 0)) :
    energy e lam F (hedgehogHiggs q) (hedgehogGauge w) =
      4 * π * (e * F) / e ^ 2 *
        ∫ s in Set.Ioi (0 : ℝ), s ^ 2 *
          radialEnergyIntegrand 1 (lam / e ^ 2) 1
            (fun s => w (s / (e * F)) / (F ^ 2 * e)) (fun s => q (s / (e * F)) / (F ^ 2 * e)) s := by sorry

end HooftMonopole
