-- Prove2me | Theorems.Thm_HooftMonopole_asymptotic_fields
-- name    : HooftMonopole.asymptotic_fields
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-23T20:12:15.502005+00:00
-- url     : https://prove2.me/theorems/ddd01705-ac41-4d53-aa83-0fac8d9ddca7
-- title:
--   Eqs. (2.18)–(2.20): far fields of the monopole and the Dirac-type electromagnetic tensor
-- statement:
--   Let $e > 0$, $F > 0$, and consider the asymptotic configuration (2.16)
--   $$Q_a(x) = F\,\frac{x_a}{r},\qquad W^a_i(x) = -\frac{\varepsilon_{iab}x_b}{er^2},\qquad r = |x| .$$
--   At every $x \neq 0$:
--   1. $D_iQ_a(x) = 0$ for all $i, a$ (eq. (2.19));
--   2. $Q_aG^a_{ij}(x) = -\dfrac{F}{er^3}\,\varepsilon_{ija}x_a$ for all $i, j$ (eq. (2.18));
--   3. the electromagnetic tensor (2.17) is
--   $$F_{ij}(x) = -\frac{1}{er^3}\,\varepsilon_{ija}x_a \qquad\text{(eq. (2.20))}.$$
--
--   So outside the core the monopole is a pure Dirac-type magnetic field of strength $1/e$ with no string.
-- source:
--   G. 't Hooft, Magnetic monopoles in unified gauge theories, Nucl. Phys. B79 (1974) 276-284, https://doi.org/10.1016/0550-3213(74)90486-6, p. 281, eqs. (2.16)-(2.20)

import Mathlib
import Definitions.Def_HooftMonopole_Defs

open MeasureTheory Filter Topology Real

namespace HooftMonopole

theorem asymptotic_fields (e F : ℝ) (he : 0 < e) (hF : 0 < F) (x : Space) (hx : x ≠ 0) :
    (∀ i a : Fin 3,
      covDeriv e (hedgehogHiggs (fun r => F / r)) (hedgehogGauge (fun r => -1 / (e * r ^ 2)))
        i x a = 0) ∧
    (∀ i j : Fin 3,
      ∑ a, hedgehogHiggs (fun r => F / r) x a *
          fieldStrength e (hedgehogGauge (fun r => -1 / (e * r ^ 2))) i j x a =
        -(F / (e * ‖x‖ ^ 3)) * ∑ a, levi i j a * x a) ∧
    (∀ i j : Fin 3,
      emField e (hedgehogHiggs (fun r => F / r)) (hedgehogGauge (fun r => -1 / (e * r ^ 2)))
          i j x =
        -(1 / (e * ‖x‖ ^ 3)) * ∑ a, levi i j a * x a) := by sorry

end HooftMonopole
