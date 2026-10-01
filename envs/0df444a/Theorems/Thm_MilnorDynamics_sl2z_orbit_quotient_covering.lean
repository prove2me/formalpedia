-- Prove2me | Theorems.Thm_MilnorDynamics_sl2z_orbit_quotient_covering
-- name    : MilnorDynamics.sl2z_orbit_quotient_covering
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T21:32:15.285592+00:00
-- url     : https://prove2.me/theorems/40c2943b-1af5-4c98-9d85-5c377b7eaf0b
-- title:
--   The orbit space of the upper half-plane by SL(2,Z) is a quotient covering of the half-plane
-- statement:
--   Let SL(2,Z) act on the upper half-plane H by Mobius transformations. This action is properly discontinuous: for any two compact sets K, L contained in H there are only finitely many gamma in SL(2,Z) with gamma K meeting L; and it is free, since a matrix fixing a point of H must be the identity. Consequently the orbit map H -> H/SL(2,Z) is a quotient covering map. This is the topological core of Milnor's Lemma 2.5: the surface in question is a quotient of a simply connected space by a properly discontinuous free action, so it has a simply connected covering space and is therefore hyperbolic. No analytic input is used here.
-- source:
--   Milnor, Dynamics in One Complex Variable, Chapter 1, Lemma 2.5; Hatcher, Algebraic Topology, Section 1.3 (properly discontinuous actions and quotient covering maps, p. 63-72). The purely topological part is formalised in Mathlib as properlyDiscontinuousSL2ZRange together with isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.

import Mathlib
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous

open scoped MatrixGroups UpperHalfPlane
open Matrix

namespace MilnorDynamics

/-- The action of the modular group `SL(2,Z)` on the upper half-plane `H` is properly
discontinuous and free, so the orbit map is a quotient covering map.  This is the purely
topological half of Milnor's Lemma 2.5: the thrice-punctured sphere is a quotient of a
simply connected space by a properly discontinuous free group action, hence admits a
simply connected covering space. -/
theorem sl2z_orbit_quotient_covering :
    IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel 𝒮ℒ ℍ)) 𝒮ℒ := by sorry

end MilnorDynamics
