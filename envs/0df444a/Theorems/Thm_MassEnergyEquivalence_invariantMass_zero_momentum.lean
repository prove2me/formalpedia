-- Prove2me | Theorems.Thm_MassEnergyEquivalence_invariantMass_zero_momentum
-- name    : MassEnergyEquivalence.invariantMass_zero_momentum
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:20:46.402827+00:00
-- url     : https://prove2.me/theorems/1ee133ea-c050-4c2f-8b46-4adf8e35b7d3
-- title:
--   Centre-of-momentum frame: invariant mass $=$ total energy $/c^2$
-- statement:
--   Let $c>0$ and consider a finite system of free particles $i\in s$ with rest masses $m_i\ge0$ and velocities $\mathbf v_i\in\mathbb R^3$, $|\mathbf v_i|<c$, with relativistic energies $E_i=\gamma_im_ic^2$ and momenta $\mathbf p_i=\gamma_im_i\mathbf v_i$. If the total momentum vanishes, $\sum_{i\in s}\mathbf p_i = 0$ (centre-of-momentum frame), then the invariant mass of the system equals its total energy divided by $c^2$:
--
--   $$
--   M = \frac{1}{c^2}\sum_{i\in s}E_i .
--   $$
--
--   In particular the kinetic energy of the constituents (e.g. of the molecules of a gas in a container) contributes to the mass of the system.
-- source:
--   Wikipedia, *Mass–energy equivalence*, https://en.wikipedia.org/wiki/Mass%E2%80%93energy_equivalence (PDF snapshot supplied by the proposer, 25 pp.), §Composite systems (p. 3): the invariant mass "is defined as the total energy (divided by $c^2$) in the center of momentum frame. The center of momentum frame is defined so that the system has zero total momentum"; container-of-gas example.

import Mathlib
import Definitions.Def_MassEnergyEquivalence_Defs

open MassEnergyEquivalence Filter Asymptotics Topology

namespace MassEnergyEquivalence

theorem invariantMass_zero_momentum {ι : Type*} (s : Finset ι) (c : ℝ) (m : ι → ℝ)
    (v : ι → Vec3) (hc : 0 < c) (hm : ∀ i ∈ s, 0 ≤ m i) (hv : ∀ i ∈ s, ‖v i‖ < c)
    (hp : ∑ i ∈ s, relMomentum c (m i) (v i) = 0) :
    invariantMass s c m v = (∑ i ∈ s, relEnergy c (m i) (v i)) / c ^ 2 := by sorry

end MassEnergyEquivalence
