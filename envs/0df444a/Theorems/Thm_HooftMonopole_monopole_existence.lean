-- Prove2me | Theorems.Thm_HooftMonopole_monopole_existence
-- name    : HooftMonopole.monopole_existence
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-23T20:15:07.925706+00:00
-- url     : https://prove2.me/theorems/ef30cdb0-4f11-4456-9987-c6964c43cace
-- title:
--   't Hooft 1974: existence of a regular magnetic monopole in the Georgi–Glashow model
-- statement:
--   Consider the static SO(3) Georgi–Glashow model with gauge coupling $e > 0$, Higgs self-coupling $\lambda > 0$ and vacuum value $F > 0$. There exist radial profiles $Q(r), W(r)$ such that the spherically symmetric configuration
--   $$Q_a(x) = x_a\,Q(|x|),\qquad W^a_i(x) = \varepsilon_{iab}\,x_b\,W(|x|)$$
--   has the following properties.
--   1. It is a regular static solution of the field equations: $Q$ and $W_i$ are $C^\infty$ on $\mathbb R^3$, the energy $E = \int(\frac14G^a_{ij}G^a_{ij} + \frac12D_iQ_aD_iQ_a + \frac18\lambda(Q_aQ_a - F^2)^2)\,d^3x$ is finite, and $E$ is stationary under all smooth compactly supported variations of $Q$ and $W$.
--   2. It satisfies the monopole boundary condition (2.6)/(2.11):
--   $$Q_a(x) - F\,\frac{x_a}{|x|} \to 0\qquad(|x|\to\infty).$$
--   3. It is a magnetic monopole: the electromagnetic tensor (2.17) has the far field (2.20),
--   $$|x|^2F_{ij}(x) + \frac1e\,\varepsilon_{ija}\frac{x_a}{|x|} \to 0\qquad(|x|\to\infty),$$
--   so the magnetic flux through large spheres tends to $4\pi/e$ in magnitude.
--
--   This is the main claim of the paper (abstract and Sect. 2): genuine magnetic monopoles arise as regular, finite-energy solutions of the field equations, with no Dirac string.
--
--   **Formalization Note** The fields are static, in the gauge $W_4 = 0$, where the remaining (Gauss-law) field equation holds automatically. Stationarity is required under all compactly supported variations, not only spherically symmetric ones.
-- source:
--   G. 't Hooft, Magnetic monopoles in unified gauge theories, Nucl. Phys. B79 (1974) 276-284, https://doi.org/10.1016/0550-3213(74)90486-6, abstract; Sect. 2 (pp. 279-281), eqs. (2.6), (2.8), (2.11), (2.16), (2.20)

import Mathlib
import Definitions.Def_HooftMonopole_Defs

open MeasureTheory Filter Topology Real

namespace HooftMonopole

theorem monopole_existence (e lam F : ℝ) (he : 0 < e) (hlam : 0 < lam) (hF : 0 < F) :
    ∃ q w : ℝ → ℝ,
      IsStaticSolution e lam F (hedgehogHiggs q) (hedgehogGauge w) ∧
      Tendsto (fun x : Space => hedgehogHiggs q x - (F / ‖x‖) • x) (cocompact Space) (𝓝 0) ∧
      ∀ i j : Fin 3,
        Tendsto (fun x : Space => ‖x‖ ^ 2 * emField e (hedgehogHiggs q) (hedgehogGauge w) i j x
            + (1 / e) * ∑ a, levi i j a * (x a / ‖x‖)) (cocompact Space) (𝓝 0) := by sorry

end HooftMonopole
