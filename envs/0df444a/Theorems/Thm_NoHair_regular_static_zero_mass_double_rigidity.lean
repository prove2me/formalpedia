-- Prove2me | Theorems.Thm_NoHair_regular_static_zero_mass_double_rigidity
-- name    : NoHair.regular_static_zero_mass_double_rigidity
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T07:37:52.543238+00:00
-- url     : https://prove2.me/theorems/aabde3dc-9eb4-4cc8-926f-463f6eb546bd
-- title:
--   Conformal doubling and rigidity from zero mass of the positive end
-- statement:
--   Take a smooth one-ended regular static vacuum slice and suppose the ADM mass of its positively rescaled end $((1+N)/2)^4h$ vanishes. Gluing the two conformal copies and filling the second infinity gives a complete scalar-flat double. Positive-mass rigidity identifies it with Euclidean three-space. The resulting global chart on the physical side carries the signed lapse, its values at the two distinguished levels, and its divergence equation on each open copy.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, section 2, equations (2.1)–(2.4), and proof of Theorem 1.1 in section 5, equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of Multiple Black Holes in Asymptotically Euclidean Static Vacuum Space-Time, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326. In the proof of Theorem 1.1, pp. 23–24 of the preprint, the rescaled end has zero mass by the ADM–Komar identity. R. Beig, Arnowitt–Deser–Misner energy and g00, Phys. Lett. A 69 (1978) 153–155, https://doi.org/10.1016/0375-9601(78)90198-6.

import Definitions.Def_NoHair_staticSliceADM

open NoHair Filter Set
open scoped Topology ContDiff Manifold

theorem NoHair.regular_static_zero_mass_double_rigidity {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D)
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric c.N c.h)) atTop (𝓝 0)) :
    let X := EuclideanSpace ℝ (Fin 3)
    ∃ (V : X → ℝ) (p : X),
      HasConformalVacuumExterior g D (fun x => 2 / (1 + V x)) ∧
      ContDiffOn ℝ 2 V ({0}ᶜ) ∧ (∀ x, x ≠ 0 → -1 < V x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x, L < ‖x‖ → |V x - 1| ≤ ε) ∧
      p ≠ 0 ∧ V p = 0 ∧ (∀ x : X, x ≠ 0 → V x ≠ 0 →
        ∑ i : Fin 3, fderiv ℝ
          (fun y => (2 / (1 + V y))^2 * fderiv ℝ V y (EuclideanSpace.single i (1:ℝ)))
          x (EuclideanSpace.single i (1:ℝ)) = 0) := by sorry
