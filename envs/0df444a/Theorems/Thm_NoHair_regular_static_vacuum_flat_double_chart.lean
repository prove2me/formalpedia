-- Prove2me | Theorems.Thm_NoHair_regular_static_vacuum_flat_double_chart
-- name    : NoHair.regular_static_vacuum_flat_double_chart
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T07:18:15.964953+00:00
-- url     : https://prove2.me/theorems/52bc5801-daee-4660-a4f4-9cd1fdfcea2e
-- title:
--   Flat doubled chart and signed lapse for a regular static vacuum slice
-- statement:
--   Double the regular one-ended static vacuum slice using $((1\pm N)/2)^4h$ and fill the second infinity by a point. The resulting complete, scalar-flat, zero-ADM-mass manifold is Euclidean by positive-mass rigidity. The asserted coordinates send the compactification point to the origin. In those coordinates the signed lapse $V$ is $C^2$ across the horizon, is greater than $-1$, tends to $1$ at spatial infinity, and vanishes at some nonzero point. With $U=2/(1+V)$, the full positive side represents the given spacetime exterior, and each open side satisfies its own static lapse equation $\operatorname{div}(U^2\nabla V)=0$.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, section 2, equations (2.1)–(2.4), and proof of Theorem 1.1 in section 5, equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of Multiple Black Holes in Asymptotically Euclidean Static Vacuum Space-Time, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326. See Proposition 3.3 and the argument immediately following equation (5.6) for regularity on the double and equality in the positive-mass theorem.

import Definitions.Def_NoHair_regularStaticVacuumSlice

open NoHair Set InnerProductSpace
open scoped ContDiff Manifold

theorem NoHair.regular_static_vacuum_flat_double_chart {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (hslice : HasRegularStaticVacuumSlice g φ D) :
    let X := EuclideanSpace ℝ (Fin 3)
    ∃ (V : X → ℝ) (p : X),
      HasConformalVacuumExterior g D (fun x => 2 / (1 + V x)) ∧
      ContDiffOn ℝ 2 V ({0}ᶜ) ∧ (∀ x, x ≠ 0 → -1 < V x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x, L < ‖x‖ → |V x - 1| ≤ ε) ∧
      p ≠ 0 ∧ V p = 0 ∧ (∀ x : X, x ≠ 0 → V x ≠ 0 →
        ∑ i : Fin 3, fderiv ℝ
          (fun y => (2 / (1 + V y))^2 * fderiv ℝ V y (EuclideanSpace.single i (1:ℝ)))
          x (EuclideanSpace.single i (1:ℝ)) = 0) := by sorry
