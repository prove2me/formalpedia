-- Prove2me | Theorems.Thm_NoHair_static_conformal_horizon_matching_forms
-- name    : NoHair.static_conformal_horizon_matching_forms
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T09:36:47.395257+00:00
-- url     : https://prove2.me/theorems/c0f6c3fd-86ec-4dbf-a589-d2e4d94da2dd
-- title:
--   Matching second fundamental forms at the conformal gluing surface
-- statement:
--   Let $h_\pm=((1\pm N)/2)^4h$ be the two metrics on the static slice. On its regular horizon both induced metrics are $h/16$ and $|\nabla N|_{h_\pm}=4\kappa$. Taking the normal pointing toward increasing $N$ on each copy, the second fundamental form of the horizon in $h_\pm$ is $\pm8\kappa$ times the common induced metric. These forms are opposites when the copies are joined. The statement expresses the normal curvature through the covariant Hessian on tangent vectors.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.static_conformal_horizon_matching_forms (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ frontier Ω, ∀ s : ℝ, s = 1 ∨ s = -1 →
      let k : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ := staticPositiveMetric (fun y => s*N y) h
      (∀ i j : Fin 3, k x i j = h x i j / 16) ∧
      staticLapseGradientSq N k x = (4*κ)^2 ∧
      ∀ v w : ADMPoint, fderiv ℝ N x v = 0 → fderiv ℝ N x w = 0 →
        (∑ i : Fin 3, ∑ j : Fin 3, staticSpatialHessian N k i j x * v i * w j) / (4*κ) =
          s*8*κ*(∑ i : Fin 3, ∑ j : Fin 3, k x i j * v i * w j) := by sorry
