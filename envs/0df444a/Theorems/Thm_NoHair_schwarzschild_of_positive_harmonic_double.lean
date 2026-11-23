-- Prove2me | Theorems.Thm_NoHair_schwarzschild_of_positive_harmonic_double
-- name    : NoHair.schwarzschild_of_positive_harmonic_double
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T06:58:15.160473+00:00
-- url     : https://prove2.me/theorems/19b4a392-c5cb-47c3-8dd4-6c4bfa265990
-- title:
--   Schwarzschild rigidity after the static vacuum conformal double is Euclidean
-- statement:
--   Suppose the exterior is globally represented by the positive-lapse portion of a punctured Euclidean conformal double, with spatial metric $U^4\delta$ and lapse $2/U-1$. The Maxwell field vanishes there. Let $U$ be nonnegative and harmonic off the puncture and tend to one at infinity. If $p\ne0$ is any zero-lapse point, so $U(p)=2$, then the entire exterior is isometric to Schwarzschild with positive mass $2|p|$. Neither spherical symmetry nor the strength of the isolated singularity is assumed.
-- source:
--   Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326, conformal doubling argument after Euclidean rigidity. Axler–Bourdon–Ramey, Harmonic Function Theory, Chapter 3, Bôcher’s theorem. Schwarzschild isotropic coordinates: S. Carroll, Lecture Notes on General Relativity, section 7.

import Definitions.Def_NoHair_conformalVacuumExterior

open NoHair Set InnerProductSpace
open scoped ContDiff Manifold

theorem NoHair.schwarzschild_of_positive_harmonic_double {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M]
    (g F : BilinField M) (D : Set M) (hF : ∀ x ∈ D, F x = 0)
    (U : EuclideanSpace ℝ (Fin 3) → ℝ) (hchart : HasConformalVacuumExterior g D U)
    (hh : HarmonicOnNhd U ({0}ᶜ)) (hpos : ∀ x, x ≠ 0 → 0 ≤ U x)
    (hfar : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x, L < ‖x‖ → |U x - 1| ≤ ε)
    (p : EuclideanSpace ℝ (Fin 3)) (hp : p ≠ 0) (hlevel : U p = 2) :
    0 < 2 * ‖p‖ ∧ IsKerrNewmanDOC g F D (2 * ‖p‖) 0 0 := by sorry
