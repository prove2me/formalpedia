-- Prove2me | Theorems.Thm_MassEnergyEquivalence_relEnergy_third_term
-- name    : MassEnergyEquivalence.relEnergy_third_term
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:15:33.764976+00:00
-- url     : https://prove2.me/theorems/4792b565-d2e3-441a-b368-52b2dcea4089
-- title:
--   Third-order approximation: $E = m_0c^2 + \tfrac12m_0v^2\big(1 + \tfrac{3v^2}{4c^2}\big) + O(v^6)$
-- statement:
--   Let $c>0$ and $m_0\ge0$. Keeping the first three terms of the power series of $E=\gamma m_0c^2$ gives an approximation that is accurate to sixth order in the speed: as $\mathbf v\to0$,
--
--   $$
--   E = m_0c^2 + \frac12 m_0v^2\left(1+\frac{3v^2}{4c^2}\right) + O(v^6),\qquad v = |\mathbf v| .
--   $$
--
--   Compared with the Newtonian approximation $E\approx m_0c^2+\tfrac12m_0v^2$, the relative correction to the kinetic term is $\tfrac{3v^2}{4c^2}$.
-- source:
--   Wikipedia, *Mass–energy equivalence*, https://en.wikipedia.org/wiki/Mass%E2%80%93energy_equivalence (PDF snapshot supplied by the proposer, 25 pp.), §Low-speed approximation (p. 6): "adding in the third term yields $E \approx m_0c^2 + \tfrac12 m_0v^2\left(1 + \tfrac{3v^2}{4c^2}\right)$".

import Mathlib
import Definitions.Def_MassEnergyEquivalence_Defs

open MassEnergyEquivalence Filter Asymptotics Topology

namespace MassEnergyEquivalence

theorem relEnergy_third_term (c m : ℝ) (hc : 0 < c) (hm : 0 ≤ m) :
    (fun v : Vec3 => relEnergy c m v
        - (m * c ^ 2 + 1 / 2 * m * ‖v‖ ^ 2 * (1 + 3 * ‖v‖ ^ 2 / (4 * c ^ 2)))) =O[𝓝 0]
      (fun v : Vec3 => ‖v‖ ^ 6) := by sorry

end MassEnergyEquivalence
