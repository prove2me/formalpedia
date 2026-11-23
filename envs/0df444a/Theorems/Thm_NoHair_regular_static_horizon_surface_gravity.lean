-- Prove2me | Theorems.Thm_NoHair_regular_static_horizon_surface_gravity
-- name    : NoHair.regular_static_horizon_surface_gravity
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T09:16:48.238542+00:00
-- url     : https://prove2.me/theorems/b3797edb-29b1-40b3-b048-cfe34383811e
-- title:
--   Positive constant surface gravity on the regular static horizon
-- statement:
--   On the connected regular horizon of the static slice the full spatial Hessian of the lapse vanishes. The squared norm of its gradient has zero derivative there and takes the single value $\kappa^2$ for some $\kappa>0$. Since $N$ is a regular defining function, the vanishing tangential Hessian is the totally geodesic boundary condition.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.regular_static_horizon_surface_gravity {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D) (heq : StaticSliceEquations c.Ω c.N c.h) :
    StaticHorizonGeometry c.Ω c.N c.h := by sorry
