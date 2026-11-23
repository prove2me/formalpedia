-- Prove2me | Theorems.Thm_NoHair_spacetime_chart_of_static_spatial_isometry
-- name    : NoHair.spacetime_chart_of_static_spatial_isometry
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T09:17:05.061115+00:00
-- url     : https://prove2.me/theorems/728474de-ee82-43c9-9271-2a6701a92d0c
-- title:
--   Lift the conformal spatial isometry to the full static spacetime chart
-- statement:
--   A Euclidean isometry of the positive conformal spatial metric which transports the lapse to $V$ lifts by keeping the time coordinate fixed. It gives the spacetime form $-V^2dt^2+(2/(1+V))^4\delta$ on the whole positive-lapse exterior, with a smooth inverse inherited from the given static spacetime chart.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.spacetime_chart_of_static_spatial_isometry {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D)
    (V : ADMPoint → ℝ) (hV : ∀ x, x ≠ 0 → -1 < V x)
    (hs : HasStaticSpatialDoubleChart c.Ω c.N c.h V) :
    HasConformalVacuumExterior g D (fun x => 2 / (1 + V x)) := by sorry
