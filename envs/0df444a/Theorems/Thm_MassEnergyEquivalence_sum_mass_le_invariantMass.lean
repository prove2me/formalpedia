-- Prove2me | Theorems.Thm_MassEnergyEquivalence_sum_mass_le_invariantMass
-- name    : MassEnergyEquivalence.sum_mass_le_invariantMass
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:21:22.129411+00:00
-- url     : https://prove2.me/theorems/93f9c75e-b101-4ef0-8c2a-4bf24ad7a3bb
-- title:
--   Mass is not additive: $\sum_i m_i \le M$, with equality iff the constituents are mutually at rest
-- statement:
--   Let $c>0$ and consider a finite system of free (non-interacting) particles $i\in s$ with rest masses $m_i\ge0$ and velocities $\mathbf v_i\in\mathbb R^3$, $|\mathbf v_i|<c$. Let $M$ be the invariant mass of the system. Then
--
--   $$
--   \sum_{i\in s} m_i \;\le\; M ,
--   $$
--
--   and, if every $m_i>0$, equality holds if and only if all the particles have the same velocity, i.e. they are at rest as observed from the centre-of-momentum frame.
--
--   Thus the mass of a system is in general not the sum of the masses of its parts: the kinetic energy of the constituents in the centre-of-momentum frame contributes to the rest mass, and the masses add up only if the constituents are at rest in that frame and do not interact.
-- source:
--   Wikipedia, *Mass–energy equivalence*, https://en.wikipedia.org/wiki/Mass%E2%80%93energy_equivalence (PDF snapshot supplied by the proposer, 25 pp.), §Mass in special relativity (p. 2): "the rest mass is almost never additive … The rest mass of an object is the total energy of all the parts, including kinetic energy, as observed from the center of momentum frame … The masses add up only if the constituents are at rest (as observed from the center of momentum frame) and do not attract or repel".

import Mathlib
import Definitions.Def_MassEnergyEquivalence_Defs

open MassEnergyEquivalence Filter Asymptotics Topology

namespace MassEnergyEquivalence

theorem sum_mass_le_invariantMass {ι : Type*} (s : Finset ι) (c : ℝ) (m : ι → ℝ)
    (v : ι → Vec3) (hc : 0 < c) (hm : ∀ i ∈ s, 0 ≤ m i) (hv : ∀ i ∈ s, ‖v i‖ < c) :
    ∑ i ∈ s, m i ≤ invariantMass s c m v ∧
      ((∀ i ∈ s, 0 < m i) →
        (invariantMass s c m v = ∑ i ∈ s, m i ↔ ∀ i ∈ s, ∀ j ∈ s, v i = v j)) := by sorry

end MassEnergyEquivalence
