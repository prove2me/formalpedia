-- Prove2me | Theorems.Thm_NoHair_static_vacuum_conformal_double
-- name    : NoHair.static_vacuum_conformal_double
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T22:27:52.073107+00:00
-- url     : https://prove2.me/theorems/e4aea523-0579-4589-b084-cfc4e3fe8017
-- title:
--   Euclidean conformal double of a static vacuum black-hole exterior
-- statement:
--   Take a smooth stationary vacuum black hole with the asymptotically flat end, complete symmetry flow, globally hyperbolic domain of outer communications $D$, nonempty black-hole region, and connected future event horizon in the 1967 milestone. Assume the stationary flow is hypersurface-orthogonal on $D$.
--
--   The proposed geometric step constructs a positive constant $b$ and a harmonic function $U$ on $\mathbb R^3\setminus\{0\}$ such that $U\to1$ at infinity and $|x|U(x)\to b$ at the puncture. The entire exterior $D$ is identified with $\mathbb R\times\{x\ne0:U(x)<2\}$, with metric
--   $$- (2/U-1)^2dt^2+U^4\,dx\cdot dx.$$
--   The horizon level set and all angular dependence are left to be determined by the harmonic problem.
--
--   In the Bunting–Masood-ul-Alam approach the Euclidean space arises by conformally rescaling and doubling a regular static slice, compactifying the other asymptotic end, and applying zero-mass rigidity. Establishing the required slice, completeness, and compactification from this milestone's causal hypotheses is part of this subproblem.
-- source:
--   Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. P. T. Chruściel, Class. Quantum Grav. 16 (1999), Theorems 1.1 and 1.3, https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf, states explicit slice assumptions.

import Definitions.Def_NoHair_conformalVacuumExterior

open NoHair Set InnerProductSpace
open scoped ContDiff Manifold

theorem NoHair.static_vacuum_conformal_double {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0)
    (hstatic : IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ (b : ℝ) (U : EuclideanSpace ℝ (Fin 3) → ℝ), 0 < b ∧ HarmonicOnNhd U ({0}ᶜ) ∧
      (∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x, L < ‖x‖ → |U x - 1| ≤ ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x, 0 < ‖x‖ → ‖x‖ < δ → |‖x‖ * U x - b| ≤ ε) ∧
      HasConformalVacuumExterior g (domainOfOuterCommunications g T E.region) U := by sorry
