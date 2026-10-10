-- Prove2me | Theorems.Thm_MassEnergyEquivalence_kineticEnergy_low_speed
-- name    : MassEnergyEquivalence.kineticEnergy_low_speed
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:14:54.688992+00:00
-- url     : https://prove2.me/theorems/bff8f47f-1fdd-478b-b076-e9783521f41a
-- title:
--   Correspondence principle: $E_k = \tfrac12 m_0v^2 + O(v^4)$
-- statement:
--   Let $c>0$ and $m_0\ge0$. The relativistic kinetic energy $E_k = m_0c^2(\gamma-1)$ of a body moving with velocity $\mathbf v\in\mathbb R^3$ agrees with the Newtonian kinetic energy up to fourth order in the speed: as $\mathbf v\to 0$,
--
--   $$
--   E_k = m_0c^2\left(\frac{1}{\sqrt{1-v^2/c^2}}-1\right) = \frac12 m_0v^2 + O(v^4),\qquad v=|\mathbf v| .
--   $$
--
--   Subtracting the rest energy $m_0c^2$ is what makes the energy of a slowly moving body agree with classical mechanics (correspondence principle); equivalently, for low speeds all but the first two terms of $E\approx m_0c^2+\tfrac12m_0v^2$ can be ignored.
-- source:
--   Wikipedia, *Mass–energy equivalence*, https://en.wikipedia.org/wiki/Mass%E2%80%93energy_equivalence (PDF snapshot supplied by the proposer, 25 pp.), §History → Mass–velocity relationship (pp. 10–11): $E_k = m_0c^2(\gamma-1)$ and "for small velocities … $E_k = \tfrac12 m_0v^2 + \cdots$"; §Low-speed approximation (p. 6): $E \approx m_0c^2 + \tfrac12 m_0v^2$.

import Mathlib
import Definitions.Def_MassEnergyEquivalence_Defs

open MassEnergyEquivalence Filter Asymptotics Topology

namespace MassEnergyEquivalence

theorem kineticEnergy_low_speed (c m : ℝ) (hc : 0 < c) (hm : 0 ≤ m) :
    (fun v : Vec3 => kineticEnergy c m v - 1 / 2 * m * ‖v‖ ^ 2) =O[𝓝 0]
      (fun v : Vec3 => ‖v‖ ^ 4) := by sorry

end MassEnergyEquivalence
