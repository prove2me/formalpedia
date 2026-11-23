-- Prove2me | Theorems.Thm_NoHair_positive_static_end_length_lower_bound
-- name    : NoHair.positive_static_end_length_lower_bound
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T08:06:38.573088+00:00
-- url     : https://prove2.me/theorems/5f77a237-1193-4423-aced-db1f5806f583
-- title:
--   Completeness at infinity of the positive static conformal end
-- statement:
--   On a sufficiently distant coordinate tail the positive conformal metric $h_+=((1+N)/2)^4h$ dominates one quarter of the Euclidean metric. For every $C^1$ curve segment in that tail, its Euclidean endpoint displacement is at most twice its $h_+$-length. In particular a curve escaping to spatial infinity has infinite length.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Theorem 5.2 (p. 22 of the preprint) and its use after (5.6) on p. 24, https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. The scalar-flat one-ended case is used here. The metric falloff is (2.1) with exponent one and two derivatives. Direct quantitative consequence of the falloff (2.1), the lapse normalization, and the positive metric in (5.6).

import Definitions.Def_NoHair_staticSliceADM

open NoHair Filter Set
open scoped Topology ContDiff Manifold

theorem NoHair.positive_static_end_length_lower_bound {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D) :
    ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric c.N c.h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric c.N c.h (γ t) i j * deriv γ t i * deriv γ t j) := by sorry
