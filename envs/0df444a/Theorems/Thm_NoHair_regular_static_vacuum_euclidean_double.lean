-- Prove2me | Theorems.Thm_NoHair_regular_static_vacuum_euclidean_double
-- name    : NoHair.regular_static_vacuum_euclidean_double
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T07:12:45.804987+00:00
-- url     : https://prove2.me/theorems/b7458035-5589-4c70-80df-4487ba8e21cd
-- title:
--   Euclidean conformal double of a regular static vacuum slice
-- statement:
--   Start with a regular, one-ended, asymptotically flat static vacuum slice with nonempty connected nondegenerate horizon, given in a global spatial chart. After conformally doubling across the horizon and compactifying the second end, the positive-mass rigidity argument gives Euclidean coordinates on the double. Taking the compactification point as the origin, the physical exterior has spatial metric $U^4\delta$ and lapse $2/U-1$ on the full side $U<2$. The function $U$ is nonnegative and harmonic off that point, tends to one at infinity, and takes the horizon value two at a nonzero point.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, section 2, equations (2.1)–(2.4), and proof of Theorem 1.1 in section 5, equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of Multiple Black Holes in Asymptotically Euclidean Static Vacuum Space-Time, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326. This is the geometric part of the proof specialized to a global spatial chart. The single puncture is the compactification point in equation (5.6).

import Definitions.Def_NoHair_regularStaticVacuumSlice

open NoHair Set InnerProductSpace
open scoped ContDiff Manifold

theorem NoHair.regular_static_vacuum_euclidean_double {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (hslice : HasRegularStaticVacuumSlice g φ D) :
    ∃ (U : EuclideanSpace ℝ (Fin 3) → ℝ) (p : EuclideanSpace ℝ (Fin 3)),
      HasConformalVacuumExterior g D U ∧ HarmonicOnNhd U ({0}ᶜ) ∧
      (∀ x, x ≠ 0 → 0 ≤ U x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x, L < ‖x‖ → |U x - 1| ≤ ε) ∧ p ≠ 0 ∧ U p = 2 := by sorry
