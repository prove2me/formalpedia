-- Prove2me | Theorems.Thm_NoHair_regular_static_slice_field_equations
-- name    : NoHair.regular_static_slice_field_equations
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T09:16:49.538471+00:00
-- url     : https://prove2.me/theorems/ccbafb39-6965-4d72-8f24-a35ede2b046f
-- title:
--   Exact static vacuum equations through the horizon
-- statement:
--   In a regular static vacuum chart the lapse and the spatial metric satisfy $D^2_hN=N\,\mathrm{Ric}_h$ and $\Delta_hN=0$ throughout the closure of the physical slice. The spacetime inverse metric is singular at $N=0$. Derive the identities on the positive side and extend the spatial tensors by continuity.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.regular_static_slice_field_equations {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D) :
    StaticSliceEquations c.Ω c.N c.h := by sorry
