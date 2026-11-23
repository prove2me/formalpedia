-- Prove2me | Theorems.Thm_NoHair_unbounded_euclidean_open_set_contains_exterior
-- name    : NoHair.unbounded_euclidean_open_set_contains_exterior
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:59:10.730743+00:00
-- url     : https://prove2.me/theorems/208009ea-baa0-414d-bf35-e0dadd94d66d
-- title:
--   An unbounded Euclidean open set with compact frontier contains a full exterior
-- statement:
--   Choose a ball containing the frontier. Its exterior is connected because it is the radial image of the product of a sphere and an interval. It cannot meet both the open set and the exterior of its closure, and unboundedness forces it into the given set.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.unbounded_euclidean_open_set_contains_exterior (U : Set ADMPoint) (op : IsOpen U) (unbounded : ¬ Bornology.IsBounded U)
    (boundary : IsCompact (frontier U)) : ∃ R : ℝ, {x : ADMPoint | R < ‖x‖} ⊆ U := by sorry
