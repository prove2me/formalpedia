-- Prove2me | Theorems.Thm_NoHair_complete_scalar_flat_adm_mass_nonnegative
-- name    : NoHair.complete_scalar_flat_adm_mass_nonnegative
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T10:49:26.826277+00:00
-- url     : https://prove2.me/theorems/52300797-c400-493f-b2d2-e4e5d0c61acf
-- title:
--   Positive mass inequality for complete scalar-flat three-manifolds
-- statement:
--   The ADM mass of a smooth complete connected scalar-flat three-manifold with a single asymptotically flat end is nonnegative. The statement allows nonorientable carriers. In a spin proof this case requires passing to the orientation cover and applying the multi-ended inequality to a lift of the chosen end.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.complete_scalar_flat_adm_mass_nonnegative (mass : ℝ) (h : IsScalarFlatADMMass mass) : 0 ≤ mass := by sorry
