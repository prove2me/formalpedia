-- Prove2me | Theorems.Thm_MassEnergyEquivalence_invariant_under_boost
-- name    : MassEnergyEquivalence.invariant_under_boost
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:18:30.440317+00:00
-- url     : https://prove2.me/theorems/cdefa5ef-fa81-4002-9bfe-b4aa2cca5bd6
-- title:
--   Rest mass is frame-independent: $E^2 - c^2|\mathbf p|^2$ is boost-invariant
-- statement:
--   Let $c>0$ and let $u$ be a speed with $|u|<c$. For an energy $E$ and momentum $\mathbf p=(p_1,p_2,p_3)$ measured in one inertial frame, let $(E',\mathbf p')$ be the energy and momentum measured in a frame moving with velocity $u$ along the first axis:
--
--   $$
--   E' = \gamma_u\,(E - u\,p_1),\qquad \mathbf p' = \Big(\gamma_u\big(p_1 - \tfrac{uE}{c^2}\big),\,p_2,\,p_3\Big),\qquad \gamma_u = \frac{1}{\sqrt{1-u^2/c^2}} .
--   $$
--
--   Then
--
--   $$
--   E'^2 - c^2|\mathbf p'|^2 = E^2 - c^2|\mathbf p|^2 .
--   $$
--
--   Since by the energy–momentum relation $E^2-c^2|\mathbf p|^2 = (m_0c^2)^2$, the rest (invariant) mass is the same for all inertial frames, independent of the motion of the observer; this holds equally for the total energy and momentum of a system of particles, whose invariant mass is the same for all observers.
--
--   **Formalization Note** Only boosts along the first coordinate axis are covered; together with rotations (which preserve $|\mathbf p|$) they generate all changes of inertial frame. $E$ and $\mathbf p$ are arbitrary, so the statement applies both to single particles and to system totals.
-- source:
--   Wikipedia, *Mass–energy equivalence*, https://en.wikipedia.org/wiki/Mass%E2%80%93energy_equivalence (PDF snapshot supplied by the proposer, 25 pp.), §Mass in special relativity (p. 2): "The rest mass is the same for all inertial frames, as it is independent of the motion of the observer"; §Composite systems (p. 3): "the invariant mass of the system … is the same for all observers, even those in relative motion".

import Mathlib
import Definitions.Def_MassEnergyEquivalence_Defs

open MassEnergyEquivalence Filter Asymptotics Topology

namespace MassEnergyEquivalence

theorem invariant_under_boost (c u E : ℝ) (p : Vec3) (hc : 0 < c) (hu : |u| < c) :
    boostEnergy c u E p ^ 2 - c ^ 2 * ‖boostMomentum c u E p‖ ^ 2 = E ^ 2 - c ^ 2 * ‖p‖ ^ 2 := by sorry

end MassEnergyEquivalence
