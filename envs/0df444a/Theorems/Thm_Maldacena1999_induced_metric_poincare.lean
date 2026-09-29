-- Prove2me | Theorems.Thm_Maldacena1999_induced_metric_poincare
-- name    : Maldacena1999.induced_metric_poincare
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T17:26:12.0539+00:00
-- url     : https://prove2.me/theorems/65b100ba-d2ae-4e85-9e54-37459805e962
-- title:
--   Induced metric on $\mathrm{AdS}_{p+2}$ in Poincaré coordinates: $\frac{U^2}{R^2}dx^2+R^2\frac{dU^2}{U^2}$
-- statement:
--   Let $p\ge0$, $R>0$, $U>0$, $x\in\mathbb R^{1,p}$, and let $\Phi_R$ be the Poincaré parametrisation (A.2) of $\mathrm{AdS}_{p+2}(R)\subset\mathbb R^{2,p+1}$. For every tangent vector $(\delta U,\delta x)\in\mathbb R\times\mathbb R^{1,p}$, the flat ambient metric $\eta$ evaluated on its image under the differential of $\Phi_R$ is
--   $$\big\langle d\Phi_R(U,x)[\delta U,\delta x],\ d\Phi_R(U,x)[\delta U,\delta x]\big\rangle_\eta=\frac{U^2}{R^2}\,\delta x^2+R^2\,\frac{\delta U^2}{U^2},$$
--   where $\delta x^2=-\delta x_0^2+\delta x_1^2+\cdots+\delta x_p^2$.
--
--   This identifies the metric $\frac{U^2}{R^2}dx^2+R^2\frac{dU^2}{U^2}$ used in the body of the paper (e.g. in (2.3)) as the metric induced on the anti-de Sitter hyperboloid.
--
--   **Formalization Note** The differential is Lean's Fréchet derivative `fderiv` of the map $(U,x)\mapsto X$ on $\mathbb R\times\mathbb R^{p+1}$.
-- source:
--   J. Maldacena, The Large-N Limit of Superconformal Field Theories and Supergravity, Int. J. Theor. Phys. 38 (1999) 1113-1133, https://doi.org/10.1023/A:1026654312961 (arXiv:hep-th/9711200), Appendix, eq. (A.3), p. 1130

import Mathlib
import Definitions.Def_Maldacena1999_Defs

open Filter Topology

namespace Maldacena1999

theorem induced_metric_poincare (p : ℕ) (R : ℝ) (hR : 0 < R)
    (U : ℝ) (hU : 0 < U) (x : Fin (p + 1) → ℝ) (δ : ℝ × (Fin (p + 1) → ℝ)) :
    ambientForm p (fderiv ℝ (poincareEmbedding p R) (U, x) δ) =
      U ^ 2 / R ^ 2 * minkowskiForm p δ.2 + R ^ 2 * δ.1 ^ 2 / U ^ 2 := by
  sorry

end Maldacena1999
