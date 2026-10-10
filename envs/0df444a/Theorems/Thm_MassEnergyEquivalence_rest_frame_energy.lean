-- Prove2me | Theorems.Thm_MassEnergyEquivalence_rest_frame_energy
-- name    : MassEnergyEquivalence.rest_frame_energy
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:11:34.058455+00:00
-- url     : https://prove2.me/theorems/b68df813-945b-40de-bcff-50486d0ead25
-- title:
--   $E = mc^2$ in the rest frame
-- statement:
--   Let $c>0$ and let $m\ge0$ be the rest mass of a body. In its rest frame (velocity $\mathbf v=0$) the body has zero relativistic momentum, and its relativistic energy equals its mass times the speed of light squared:
--
--   $$
--   \mathbf p = 0,\qquad E = mc^2 .
--   $$
--
--   This is Einstein's formula, which defines the energy of a particle in its rest frame as the product of its mass with the speed of light squared.
-- source:
--   Wikipedia, *Mass–energy equivalence*, https://en.wikipedia.org/wiki/Mass%E2%80%93energy_equivalence (PDF snapshot supplied by the proposer, 25 pp.), lead section and §The formula (p. 1): "$E=mc^2$ … defines the energy $E$ of a particle in its rest frame as the product of mass $m$ with the speed of light squared $c^2$"; §Description (p. 1): in the rest frame the object has no momentum.

import Mathlib
import Definitions.Def_MassEnergyEquivalence_Defs

open MassEnergyEquivalence Filter Asymptotics Topology

namespace MassEnergyEquivalence

theorem rest_frame_energy (c m : ℝ) (hc : 0 < c) (hm : 0 ≤ m) :
    relMomentum c m 0 = 0 ∧ relEnergy c m 0 = m * c ^ 2 := by sorry

end MassEnergyEquivalence
