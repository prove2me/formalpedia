-- Prove2me | Theorems.Thm_NoHair_static_vacuum_linearized_einstein_decay
-- name    : NoHair.static_vacuum_linearized_einstein_decay
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T07:52:49.037467+00:00
-- url     : https://prove2.me/theorems/30ff9506-85d5-4820-840d-e3a2af2784ea
-- title:
--   Quadratic decay of the linearized Einstein residual on a static vacuum end
-- statement:
--   In static Cartesian coordinates let $k_{ij}=h_{ij}+2(N-1)\delta_{ij}$. Every component of the Euclidean linearized Einstein tensor of $k$ is $O(r^{-4})$. The static vacuum equation cancels the $O(r^{-3})$ principal terms. The expected errors are products of first derivatives or of an $O(r^{-1})$ coefficient perturbation with a second derivative. This estimate is local on the asymptotic end.
-- source:
--   P. Miao and L.-F. Tam, Evaluation of the ADM mass and center of mass via the Ricci tensor, Proc. Amer. Math. Soc. 144 (2016), pp. 753–761, Theorem 1.1(a) and the Euclidean integration-by-parts identity in the proof of Theorem 2.1, equations (2.2)–(2.8), https://arxiv.org/abs/1408.3893, https://doi.org/10.1090/proc12726. Apply the curvature expansions of equation (2.2) to the static vacuum equations (5.4)–(5.5) in P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, section 2, equations (2.1)–(2.4), and proof of Theorem 1.1 in section 5, equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of Multiple Black Holes in Asymptotically Euclidean Static Vacuum Space-Time, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_linearADMFlux

open Set Filter MeasureTheory NoHair
open scoped ContDiff Manifold Topology

theorem NoHair.static_vacuum_linearized_einstein_decay {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ x : ADMPoint, R < ‖x‖ → ∀ i j : Fin 3,
      |negativeTwiceLinearEinstein (lapseCorrectedADMMetric c.N c.h) i j x| ≤ C / ‖x‖^4 := by sorry
