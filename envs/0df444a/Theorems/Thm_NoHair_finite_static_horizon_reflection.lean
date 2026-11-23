-- Prove2me | Theorems.Thm_NoHair_finite_static_horizon_reflection
-- name    : NoHair.finite_static_horizon_reflection
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T10:50:53.778146+00:00
-- url     : https://prove2.me/theorems/ef284cc1-de31-4fb4-bef6-e3a1f995c916
-- title:
--   Smooth reflection of the two finite static copies across the horizon
-- statement:
--   Double the closed spatial slice along the regular zero-lapse boundary, retaining both unfilled infinities. On each copy the metric and the signed lapse have been calculated in the original coordinates. The remaining local work is smoothness through the seam and coordinate invariance of the curvature and lapse equations. A Gaussian normal collar and the static equations give the parity of the normal jets.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.finite_static_horizon_reflection (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (hflat : ∀ x ∈ closure Ω, spatialScalarCurvature h x = 0 ∧
      ∀ s : ℝ, 1 + s * N x ≠ 0 →
        spatialScalarCurvature (staticPositiveMetric (fun y => s*N y) h) x = 0)
    (hforms : ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ frontier Ω, ∀ s : ℝ, s = 1 ∨ s = -1 →
      let k : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ := staticPositiveMetric (fun y => s*N y) h
      (∀ i j : Fin 3, k x i j = h x i j / 16) ∧
      staticLapseGradientSq N k x = (4*κ)^2 ∧
      ∀ v w : ADMPoint, fderiv ℝ N x v = 0 → fderiv ℝ N x w = 0 →
        (∑ i : Fin 3, ∑ j : Fin 3, staticSpatialHessian N k i j x * v i * w j) / (4*κ) =
          s*8*κ*(∑ i : Fin 3, ∑ j : Fin 3, k x i j * v i * w j))
    (hgood : ∀ x ∈ closure Ω, 0 ≤ N x ∧ N x < 1 ∧ ∀ s : ℝ, s=1 ∨ s=-1 →
      let k : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ := staticPositiveMetric (fun y => s*N y) h
      (k x).PosDef ∧ spatialScalarCurvature k x = 0)
    (hdiv : ∀ x ∈ closure Ω, ∀ s : ℝ, s=1 ∨ s=-1 →
      staticWeightedLapseDivergence (staticPositiveMetric (fun y => s*N y) h) (fun y => s*N y) x = 0) :
    Nonempty (ReflectedStaticDouble Ω N h) := by sorry
