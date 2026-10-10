-- Prove2me | Theorems.Thm_MassEnergyEquivalence_energy_momentum_relation
-- name    : MassEnergyEquivalence.energy_momentum_relation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:21:50.18239+00:00
-- url     : https://prove2.me/theorems/0b8a418c-bb69-4697-81ea-92fc031331d0
-- title:
--   Energy–momentum relation: $E_{\mathrm{rel}}^2 - |\mathbf p|^2c^2 = m_0^2c^4$
-- statement:
--   Let $c>0$ be the speed of light, let $m_0\ge 0$ be the rest mass of a body, and let $\mathbf v\in\mathbb R^3$ be its velocity, with $|\mathbf v|<c$. With Lorentz factor $\gamma=1/\sqrt{1-|\mathbf v|^2/c^2}$, relativistic energy $E_{\mathrm{rel}}=\gamma m_0c^2$ and relativistic momentum $\mathbf p=\gamma m_0\mathbf v$,
--
--   $$
--   E_{\mathrm{rel}}^2 - |\mathbf p|^2c^2 = m_0^2c^4 .
--   $$
--
--   This is the extension of Einstein's formula $E=mc^2$ to systems in motion (the **energy–momentum relation**): the relativistic energy depends on both the rest mass and the momentum, and it reduces to $E_{\mathrm{rel}}=m_0c^2$ when the momentum vanishes.
--
--   **Formalization Note** The body is modelled by its rest mass and velocity; energy and momentum are the derived quantities $\gamma m_0c^2$ and $\gamma m_0\mathbf v$ from the mission's definition file.
-- source:
--   Wikipedia, *Mass–energy equivalence*, https://en.wikipedia.org/wiki/Mass%E2%80%93energy_equivalence (PDF snapshot supplied by the proposer, 25 pp.), §Extension for systems in motion (pp. 5–6), first display: $E_{\mathrm{rel}}^2 - |\mathbf p|^2c^2 = m_0^2c^4$; with $E=\gamma mc^2$ from §Low-speed approximation (p. 6).

import Mathlib
import Definitions.Def_MassEnergyEquivalence_Defs

open MassEnergyEquivalence Filter Asymptotics Topology

namespace MassEnergyEquivalence

theorem energy_momentum_relation (c m : ℝ) (v : Vec3) (hc : 0 < c) (hm : 0 ≤ m)
    (hv : ‖v‖ < c) :
    relEnergy c m v ^ 2 - ‖relMomentum c m v‖ ^ 2 * c ^ 2 = m ^ 2 * c ^ 4 := by sorry

end MassEnergyEquivalence
