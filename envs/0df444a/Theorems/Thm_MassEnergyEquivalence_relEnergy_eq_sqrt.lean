-- Prove2me | Theorems.Thm_MassEnergyEquivalence_relEnergy_eq_sqrt
-- name    : MassEnergyEquivalence.relEnergy_eq_sqrt
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:12:14.351013+00:00
-- url     : https://prove2.me/theorems/e04a5440-a388-4157-a52e-7722668f81e1
-- title:
--   $E_{\mathrm{rel}} = \sqrt{(m_0c^2)^2 + (pc)^2}$
-- statement:
--   Let $c>0$, $m_0\ge 0$ and $\mathbf v\in\mathbb R^3$ with $|\mathbf v|<c$. With $E_{\mathrm{rel}}=\gamma m_0c^2$, $\mathbf p=\gamma m_0\mathbf v$ and $p=|\mathbf p|$,
--
--   $$
--   E_{\mathrm{rel}} = \sqrt{(m_0c^2)^2 + (pc)^2}.
--   $$
--
--   This is the third form of the energy–momentum relation given in the article; it exhibits the relativistic energy as a function of rest mass and momentum, and reduces to $E_{\mathrm{rel}}=m_0c^2$ when $p=0$.
-- source:
--   Wikipedia, *Mass–energy equivalence*, https://en.wikipedia.org/wiki/Mass%E2%80%93energy_equivalence (PDF snapshot supplied by the proposer, 25 pp.), §Extension for systems in motion (p. 6), third display: $E_{\mathrm{rel}} = \sqrt{(m_0c^2)^2 + (pc)^2}$.

import Mathlib
import Definitions.Def_MassEnergyEquivalence_Defs

open MassEnergyEquivalence Filter Asymptotics Topology

namespace MassEnergyEquivalence

theorem relEnergy_eq_sqrt (c m : ℝ) (v : Vec3) (hc : 0 < c) (hm : 0 ≤ m) (hv : ‖v‖ < c) :
    relEnergy c m v = Real.sqrt ((m * c ^ 2) ^ 2 + (‖relMomentum c m v‖ * c) ^ 2) := by sorry

end MassEnergyEquivalence
