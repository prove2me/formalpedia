-- Prove2me | Theorems.Thm_NoHair_euclidean_chart_from_static_completion
-- name    : NoHair.euclidean_chart_from_static_completion
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:08:36.38281+00:00
-- url     : https://prove2.me/theorems/2bb3f845-782f-4256-93fd-eb6fa8efdcee
-- title:
--   Euclidean exterior coordinates from rigidity of the completed double
-- statement:
--   Apply the equality case of the positive-mass theorem to the complete abstract static conformal double. Send the compactification point to the origin by a translation. The induced spatial chart covers its entire positive-lapse region, the signed lapse has the specified limits, and its Riemannian weighted divergence equation becomes the Cartesian one.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticConformalCompletion

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.euclidean_chart_from_static_completion (Ω : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (d : StaticConformalCompletion Ω N h) (hrigidity : ThreeDimensionalZeroMassRigidity) :
    ∃ (V : ADMPoint → ℝ) (p : ADMPoint), HasStaticSpatialDoubleChart Ω N h V ∧
      ContDiffOn ℝ 2 V ({0}ᶜ) ∧ (∀ x, x ≠ 0 → -1 < V x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x, L < ‖x‖ → |V x - 1| ≤ ε) ∧
      p ≠ 0 ∧ V p = 0 ∧ (∀ x : ADMPoint, x ≠ 0 → V x ≠ 0 →
        ∑ i : Fin 3, fderiv ℝ
          (fun y => (2 / (1 + V y))^2 * fderiv ℝ V y (EuclideanSpace.single i (1:ℝ)))
          x (EuclideanSpace.single i (1:ℝ)) = 0) := by sorry
