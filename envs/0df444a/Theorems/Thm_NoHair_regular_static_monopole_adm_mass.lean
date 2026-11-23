-- Prove2me | Theorems.Thm_NoHair_regular_static_monopole_adm_mass
-- name    : NoHair.regular_static_monopole_adm_mass
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T11:46:56.230844+00:00
-- url     : https://prove2.me/theorems/1f762373-5ecc-4e2f-b850-e215dadc234e
-- title:
--   The positive lapse monopole is the ADM mass of a regular static vacuum slice
-- statement:
--   For a regular asymptotically flat static vacuum slice with compact nondegenerate horizon, three measurements give the same positive number. It is the direction-independent coefficient of the lapse defect, the limit of the normalized lapse surface flux and the limit of the coordinate ADM energy. The fluxes use the conventional factors 1/(4π) and 1/(16π).
-- source:
--   R. Beig, Arnowitt–Deser–Misner energy and g00, Phys. Lett. A 69 (1978), 153–155, https://doi.org/10.1016/0375-9601(78)90198-6. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticInvertedEndMetric

open NoHair Filter Set
open scoped Topology ContDiff Manifold

theorem NoHair.regular_static_monopole_adm_mass {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ,E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D) :
    ∃ μ : ℝ, 0 < μ ∧ HasStaticLapseMonopole c.N μ ∧
      Tendsto (staticLapseFlux c.N) atTop (𝓝 μ) ∧ Tendsto (staticADMFlux c.h) atTop (𝓝 μ) := by
  sorry
