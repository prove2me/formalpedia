-- Prove2me | Theorems.Thm_NoHair_israel_static_vacuum_regular_slice
-- name    : NoHair.israel_static_vacuum_regular_slice
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T07:12:59.975617+00:00
-- url     : https://prove2.me/theorems/2c800d0c-37a2-4980-8c8b-e87bebcb0f0f
-- title:
--   Israel static vacuum uniqueness with a timelike end and a regular slice
-- statement:
--   Choose an asymptotically flat reference end on which the stationary Killing field is everywhere timelike. Suppose its domain of outer communications admits a regular, one-ended static vacuum slice in a global spatial chart, with a smooth positive-definite spatial metric up to a connected nondegenerate zero-lapse boundary. Under the stationary vacuum black-hole hypotheses, this entire domain is isometric to a Schwarzschild exterior of positive mass. This is a strengthened-hypothesis version of the Israel milestone.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, section 2, equations (2.1)–(2.4), and proof of Theorem 1.1 in section 5, equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of Multiple Black Holes in Asymptotically Euclidean Static Vacuum Space-Time, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326. See also W. Israel, Event Horizons in Static Vacuum Space-Times, Phys. Rev. 164 (1967) 1776–1779, https://doi.org/10.1103/PhysRev.164.1776. This statement explicitly assumes a globally regular static slice; it is a coordinate special case.

import Definitions.Def_NoHair_regularStaticVacuumSlice

open NoHair Set InnerProductSpace
open scoped ContDiff Manifold

theorem NoHair.israel_static_vacuum_regular_slice {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0)
    (hstatic : IsStaticOn g φ (domainOfOuterCommunications g T E.region))
    (htime : ∀ x ∈ E.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0)
    (hslice : HasRegularStaticVacuumSlice g φ (domainOfOuterCommunications g T E.region)) :
    ∃ m : ℝ, 0 < m ∧ IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m 0 0 := by sorry
