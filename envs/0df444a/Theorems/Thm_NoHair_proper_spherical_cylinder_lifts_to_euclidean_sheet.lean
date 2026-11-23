-- Prove2me | Theorems.Thm_NoHair_proper_spherical_cylinder_lifts_to_euclidean_sheet
-- name    : NoHair.proper_spherical_cylinder_lifts_to_euclidean_sheet
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T11:06:56.174446+00:00
-- url     : https://prove2.me/theorems/21742443-1f0b-42bd-b213-9a3a90b5a8b3
-- title:
--   A proper spherical cylinder lifts to an exterior sheet with compact frontier
-- statement:
--   Lift the full sphere-times-line parametrization of a proper end across a covering from Euclidean three-space. The sphere is simply connected, so the lift exists and is an open embedding. The portion with positive cylinder coordinate has compact frontier in the lift of the slice at zero. Escape of the base end forces this sheet to be unbounded.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.proper_spherical_cylinder_lifts_to_euclidean_sheet {Q : Type*} [MetricSpace Q] [PathConnectedSpace Q]
    (e : ADMSphere × ℝ → Q) (oe : Topology.IsOpenEmbedding e)
    (far : ∀ K : Set Q, IsCompact K → ∃ T : ℝ, ∀ n : ADMSphere, ∀ t : ℝ, T<t → e (n,t) ∉ K)
    (p : ADMPoint → Q) (cover : IsCoveringMap p) :
    ∃ U : Set ADMPoint, IsOpen U ∧ ¬ Bornology.IsBounded U ∧ IsCompact (frontier U) ∧ Set.InjOn p U := by sorry
