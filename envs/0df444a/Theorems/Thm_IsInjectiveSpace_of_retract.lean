-- Prove2me | Theorems.Thm_IsInjectiveSpace_of_retract
-- name    : IsInjectiveSpace.of_retract
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:29.530313+00:00
-- url     : https://prove2.me/theorems/fd072857-89c5-4db3-9698-3f5a89900603
-- title:
--   Is Injective Space: of retract
-- statement:
--   **Scott 1972, Proposition 1.4.** Retracts of injective spaces are injective.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L69-L78
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L69-L78

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
set_option autoImplicit true
open Topology TopologicalSpace
universe u v w

theorem IsInjectiveSpace.of_retract {D : Type v} {D' : Type v}
    [TopologicalSpace D] [TopologicalSpace D'] (hD : IsInjectiveSpace.{u} D)
    (s : C(D', D)) (r : C(D, D')) (hrs : ∀ d, r (s d) = d) :
    IsInjectiveSpace.{u} D' := by sorry
