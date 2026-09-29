-- Prove2me | Theorems.Thm_HooftMonopole_asymptotic_power_law
-- name    : HooftMonopole.asymptotic_power_law
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T20:04:39.016777+00:00
-- url     : https://prove2.me/theorems/7c65eda5-0287-4c17-9d1e-703c181258ed
-- title:
--   Eqs. (2.14)–(2.15): the only power law is $W = -1/(er^2)$
-- statement:
--   Let $e > 0$, $F > 0$, $a \neq 0$ and $n \in \mathbb R$. Put $W(r) = a\,r^{-n}$ and $Q(r) = F/r$ for $r > 0$. Then $W, Q$ satisfy the Lagrange equation (2.13),
--   $$\frac{d}{dr}\Big(2r^4W' + 4r^3W\Big) = r^2\Big[4rW' + 12W + 6er^2W^2 + 2e^2r^4W^3 + 2er^2Q^2 + 2e^2r^4WQ^2\Big],$$
--   at every $r > 0$ if and only if
--   $$n = 2 \quad\text{and}\quad a = -\frac1e .$$
--
--   This identifies the far field of the monopole, $W \sim -1/(er^2)$, $Q \sim F/r$, eq. (2.16).
--
--   **Formalization Note** 't Hooft's argument matches leading powers as $r \to \infty$; here it is stated for exact power laws, where both directions are exact identities. $r^{-n}$ is the real power function for $r > 0$.
-- source:
--   G. 't Hooft, Magnetic monopoles in unified gauge theories, Nucl. Phys. B79 (1974) 276-284, https://doi.org/10.1016/0550-3213(74)90486-6, p. 280, eqs. (2.11)-(2.15)

import Mathlib
import Definitions.Def_HooftMonopole_Defs

open MeasureTheory Filter Topology Real

namespace HooftMonopole

theorem asymptotic_power_law (e F : ℝ) (he : 0 < e) (hF : 0 < F) (a n : ℝ) (ha : a ≠ 0) :
    (∀ r : ℝ, 0 < r → radialWEquation e (fun s => a * s ^ (-n)) (fun s => F / s) r) ↔
      (n = 2 ∧ a = -1 / e) := by sorry

end HooftMonopole
