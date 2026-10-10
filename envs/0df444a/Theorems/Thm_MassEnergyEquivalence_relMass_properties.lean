-- Prove2me | Theorems.Thm_MassEnergyEquivalence_relMass_properties
-- name    : MassEnergyEquivalence.relMass_properties
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:13:19.417923+00:00
-- url     : https://prove2.me/theorems/1dd3c770-f6fb-49ad-b67c-0218179deaee
-- title:
--   Relativistic mass: $m_{\mathrm{rel}} = m_0 + E_k/c^2 \ge m_0$, with equality only at rest
-- statement:
--   Let $c>0$, $m_0\ge0$ and $\mathbf v\in\mathbb R^3$ with $|\mathbf v|<c$. Let $m_{\mathrm{rel}}=E_{\mathrm{rel}}/c^2$ be the relativistic mass and $E_k=E_{\mathrm{rel}}-m_0c^2$ the kinetic energy. Then:
--
--   1. $m_{\mathrm{rel}} = m_0 + \dfrac{E_k}{c^2}$ (the relativistic mass exceeds the rest mass by the mass associated with the kinetic energy);
--   2. $m_0 \le m_{\mathrm{rel}}$ (the rest mass is the smallest possible value of the relativistic mass);
--   3. if $m_0>0$, then $m_{\mathrm{rel}} = m_0$ if and only if $\mathbf v = 0$ (a moving massive object has strictly larger relativistic mass than at rest).
--
--   $$
--   m_0 \le m_{\mathrm{rel}} = m_0 + \frac{E_k}{c^2}.
--   $$
-- source:
--   Wikipedia, *Mass–energy equivalence*, https://en.wikipedia.org/wiki/Mass%E2%80%93energy_equivalence (PDF snapshot supplied by the proposer, 25 pp.), §Mass in special relativity (p. 2): the rest mass "is the smallest possible value of the relativistic mass of the object"; §Relativistic mass (p. 2): "The relativistic mass of a moving object is larger than the relativistic mass of an object at rest … greater than the rest mass by an amount equal to the mass associated with the kinetic energy of the object"; $m_{\mathrm{rel}} = E/c^2$.

import Mathlib
import Definitions.Def_MassEnergyEquivalence_Defs

open MassEnergyEquivalence Filter Asymptotics Topology

namespace MassEnergyEquivalence

theorem relMass_properties (c m : ℝ) (v : Vec3) (hc : 0 < c) (hm : 0 ≤ m) (hv : ‖v‖ < c) :
    relMass c m v = m + kineticEnergy c m v / c ^ 2 ∧ m ≤ relMass c m v ∧
      (0 < m → (relMass c m v = m ↔ v = 0)) := by sorry

end MassEnergyEquivalence
