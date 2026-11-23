-- Prove2me | Theorems.Thm_NoHair_euclidean_riemannian_cover_deck_isometries_transitive
-- name    : NoHair.euclidean_riemannian_cover_deck_isometries_transitive
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T11:55:10.279898+00:00
-- url     : https://prove2.me/theorems/1d2c57ca-c248-40d4-ae59-4467410b390e
-- title:
--   Deck isometries act transitively on fibers of a Euclidean Riemannian covering
-- statement:
--   Lift the projection from simply connected Euclidean space twice to get inverse deck transformations carrying either specified lift to the other. Each is locally a composition of smooth isometries. Its differential preserves norms, so the Euclidean mean value inequality makes it nonexpanding. The inverse gives equality of distances.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_spatialRiemannCurvature
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Geometry.Manifold.Instances.Icc

open NoHair Set Filter Bundle
open scoped Topology ContDiff Manifold

theorem NoHair.euclidean_riemannian_cover_deck_isometries_transitive (Q : Type) [MetricSpace Q] [ChartedSpace ADMPoint Q] [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] [ConnectedSpace Q] (p : ADMPoint → Q)
    (cov : IsCoveringMap p) (dif : IsLocalDiffeomorph 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ p)
    (iso : ∀ x v w : ADMPoint, inner ℝ (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) p x v)
      (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) p x w) = inner ℝ v w) :
    ∀ x y, p x=p y → ∃ γ : ADMPoint ≃ᵢ ADMPoint, γ x=y ∧ ∀ z, p (γ z)=p z := by sorry
