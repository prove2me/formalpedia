-- Prove2me | Theorems.Thm_MassEnergyEquivalence_massless_energy_eq_pc
-- name    : MassEnergyEquivalence.massless_energy_eq_pc
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:12:39.907346+00:00
-- url     : https://prove2.me/theorems/ad4ffbb2-929e-43db-a31d-23564aa7eff0
-- title:
--   Massless particles: $E_{\mathrm{rel}} = pc$
-- statement:
--   Let $c>0$, and let $E\ge 0$ and $p\ge 0$ be the energy and momentum magnitude of a particle satisfying the energy–momentum relation $E^2-(pc)^2=(m_0c^2)^2$ with rest mass $m_0=0$. Then
--
--   $$
--   E = pc .
--   $$
--
--   For photons, which have zero rest mass, the energy–momentum relation thus reduces to $E_{\mathrm{rel}}=pc$: their energy is due only to their momentum.
--
--   **Formalization Note** A massless particle travels at speed $c$, where the Lorentz factor is undefined, so it cannot be described by the velocity-based quantities $\gamma m c^2$, $\gamma m\mathbf v$ of the definition file (with $m=0$ those would both vanish). The statement is therefore phrased directly in terms of a pair $(E,p)$ satisfying the energy–momentum relation with $m_0=0$.
-- source:
--   Wikipedia, *Mass–energy equivalence*, https://en.wikipedia.org/wiki/Mass%E2%80%93energy_equivalence (PDF snapshot supplied by the proposer, 25 pp.), §Extension for systems in motion (p. 6): "For photons where $m_0 = 0$, the equation reduces to $E_{\mathrm{rel}} = pc$"; §Mass in special relativity (p. 2): massless particles' energy is due only to their momentum.

import Mathlib
import Definitions.Def_MassEnergyEquivalence_Defs

open MassEnergyEquivalence Filter Asymptotics Topology

namespace MassEnergyEquivalence

theorem massless_energy_eq_pc (c E p : ℝ) (hc : 0 < c) (hE : 0 ≤ E) (hp : 0 ≤ p)
    (h : E ^ 2 - (p * c) ^ 2 = ((0 : ℝ) * c ^ 2) ^ 2) :
    E = p * c := by sorry

end MassEnergyEquivalence
