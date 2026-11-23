-- Prove2me | Theorems.Thm_NoHair_static_harmonic_lapse_positive_conserved_flux
-- name    : NoHair.static_harmonic_lapse_positive_conserved_flux
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:59:04.008938+00:00
-- url     : https://prove2.me/theorems/e18f7ad3-9226-46cb-8938-c24e51ad6280
-- title:
--   Strictly positive conserved flux of the harmonic static lapse
-- statement:
--   The metric volume density times the raised lapse gradient has the same strictly positive outward flux through every sufficiently large coordinate sphere. The flux is unnormalized. A smooth lapse cutoff extends its density across the horizon; its divergence has compact support, is nonnegative, and is positive at an interior point near the horizon.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.static_harmonic_lapse_positive_conserved_flux (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ m R : ℝ, 0 < m ∧ 0 < R ∧ ∀ r : ℝ, R < r →
      r^2 * (∫ n : ADMSphere, ∑ i : Fin 3,
        (Real.sqrt (h (r • (n:ADMPoint))).det * staticRaisedGradient N h i (r • (n:ADMPoint))) *
          (n:ADMPoint) i ∂admSurfaceMeasure) = m := by sorry
