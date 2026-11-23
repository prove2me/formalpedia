-- Prove2me | Theorems.Thm_NoHair_regular_static_vacuum_adm_lapse_flux
-- name    : NoHair.regular_static_vacuum_adm_lapse_flux
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T07:37:47.565949+00:00
-- url     : https://prove2.me/theorems/6ad7d15b-8264-4a59-8123-789116a1a543
-- title:
--   ADM and lapse flux agree for a regular static vacuum end
-- statement:
--   For the normalized static Killing field on a regular one-ended asymptotically flat static vacuum slice, the difference of the coordinate ADM surface energy and the Euclidean lapse flux tends to zero on large spheres. The limiting lapse flux is the Komar mass. Both integrals use the same asymptotic Cartesian chart.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, section 2, equations (2.1)–(2.4), and proof of Theorem 1.1 in section 5, equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of Multiple Black Holes in Asymptotically Euclidean Static Vacuum Space-Time, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326. In the proof of Theorem 1.1, pp. 23–24 of the preprint, the rescaled end has zero mass by the ADM–Komar identity. R. Beig, Arnowitt–Deser–Misner energy and g00, Phys. Lett. A 69 (1978) 153–155, https://doi.org/10.1016/0375-9601(78)90198-6.

import Definitions.Def_NoHair_staticSliceADM

open NoHair Filter Set
open scoped Topology ContDiff Manifold

theorem NoHair.regular_static_vacuum_adm_lapse_flux {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D) :
    Tendsto (fun r : ℝ => staticADMFlux c.h r - staticLapseFlux c.N r) atTop (𝓝 0) := by sorry
