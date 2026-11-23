-- Prove2me | Theorems.Thm_NoHair_euclidean_riemannian_cover_realizes_fiber_distance
-- name    : NoHair.euclidean_riemannian_cover_realizes_fiber_distance
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T11:55:05.897425+00:00
-- url     : https://prove2.me/theorems/5ec39a16-11a2-446b-b910-f1c0b7b502ef
-- title:
--   A Euclidean Riemannian covering realizes the base distance to each fiber
-- statement:
--   Choose a point of the fiber closest to the prescribed lift in Euclidean space. The projection preserves lengths of smooth paths. Conversely every smooth base path lifts to a smooth path of the same length from the specified lift. Taking the two infima identifies the distance to the fiber with the distance in the base.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_spatialRiemannCurvature
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Geometry.Manifold.Instances.Icc

open NoHair Set Filter Bundle
open scoped Topology ContDiff Manifold

theorem NoHair.euclidean_riemannian_cover_realizes_fiber_distance (Q : Type) [MetricSpace Q] [ChartedSpace ADMPoint Q] [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] [ConnectedSpace Q] (p : ADMPoint → Q)
    (cov : IsCoveringMap p) (dif : IsLocalDiffeomorph 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ p)
    (iso : ∀ x v w : ADMPoint, inner ℝ (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) p x v)
      (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) p x w) = inner ℝ v w) :
    ∀ x : ADMPoint, ∀ q : Q, ∃ y : ADMPoint, p y=q ∧ dist x y=dist (p x) q := by sorry
