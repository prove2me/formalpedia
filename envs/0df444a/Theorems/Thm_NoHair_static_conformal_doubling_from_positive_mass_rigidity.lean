-- Prove2me | Theorems.Thm_NoHair_static_conformal_doubling_from_positive_mass_rigidity
-- name    : NoHair.static_conformal_doubling_from_positive_mass_rigidity
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T08:06:59.657584+00:00
-- url     : https://prove2.me/theorems/7a05d8ce-b4b2-4fdb-9ebb-f783bba60875
-- title:
--   Static conformal doubling assuming the Riemannian rigidity theorem
-- statement:
--   Assume the scalar-flat, one-ended, three-dimensional equality case of the positive mass theorem. For the given regular static vacuum slice, the physical rescaling has zero ADM mass. Construct its complete scalar-flat double, use the stated Riemannian theorem to identify the double with Euclidean space, and obtain the global spacetime chart with the signed lapse and its divergence equation on both open sides. This implication isolates the geometric construction and coordinate transport from the independently stated positive-mass theorem. The quantitative length estimate on the surviving end is supplied separately.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Theorem 5.2 (p. 22 of the preprint) and its use after (5.6) on p. 24, https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. The scalar-flat one-ended case is used here. The metric falloff is (2.1) with exponent one and two derivatives. For the gluing along the horizon, second-end compactification, and static lapse equation, see Proposition 3.3 and section 5, equations (5.4)–(5.6). Bunting–Masood-ul-Alam, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_riemannianMassRigidity

open NoHair Set Filter InnerProductSpace
open scoped Manifold ContDiff Topology

theorem NoHair.static_conformal_doubling_from_positive_mass_rigidity {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D)
    (hrigidity : ThreeDimensionalZeroMassRigidity)
    (hpositiveEnd : ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric c.N c.h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric c.N c.h (γ t) i j * deriv γ t i * deriv γ t j))
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
