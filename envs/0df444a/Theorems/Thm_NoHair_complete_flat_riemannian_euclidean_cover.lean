-- Prove2me | Theorems.Thm_NoHair_complete_flat_riemannian_euclidean_cover
-- name    : NoHair.complete_flat_riemannian_euclidean_cover
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T11:46:55.094273+00:00
-- url     : https://prove2.me/theorems/5b23c3f4-b669-4d06-8f5e-b26aed2efed6
-- title:
--   Euclidean Riemannian covering of a complete flat manifold of dimension three
-- statement:
--   Construct the developing cover of a connected complete flat Riemannian three-manifold. Parallel translation of a frame on the simply connected covering yields three global parallel orthonormal fields. Their flows are complete and commute, and their joint flow identifies the cover isometrically with Euclidean space. Lifting minimizing geodesics realizes the distance to each fiber. The deck transformations preserve the lifted metric.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_spatialRiemannCurvature

open NoHair Set Filter Bundle
open scoped Topology ContDiff Manifold

theorem NoHair.complete_flat_riemannian_euclidean_cover (Q : Type) [m : MetricSpace Q] [ch : ChartedSpace ADMPoint Q] [sm : IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [rb : RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [sr : IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [rm : IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] [cm : CompleteSpace Q] [cn : ConnectedSpace Q]
    [sc : SecondCountableTopology Q]
    (flat : FlatInADMCharts Q) :
    ∃ p : ADMPoint → Q, IsCoveringMap p ∧
    IsLocalDiffeomorph 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ p ∧
    (∀ x v w : ADMPoint, inner ℝ (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) p x v)
      (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) p x w) = inner ℝ v w) ∧
    (∀ x : ADMPoint, ∀ q : Q, ∃ y : ADMPoint, p y=q ∧ dist x y=dist (p x) q) ∧
    ∀ x y, p x=p y → ∃ γ : ADMPoint ≃ᵢ ADMPoint, γ x=y ∧ ∀ z, p (γ z)=p z := by sorry
