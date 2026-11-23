-- Prove2me | Theorems.Thm_NoHair_zero_mass_ricci_flat_by_first_variation
-- name    : NoHair.zero_mass_ricci_flat_by_first_variation
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T10:49:49.762802+00:00
-- url     : https://prove2.me/theorems/102ef8ad-0a72-49d6-b895-e9c515dca92b
-- title:
--   Vanishing of Ricci at a scalar-flat ADM mass minimizer
-- statement:
--   Assuming the scalar-flat positive mass inequality, a zero-mass metric must be Ricci flat. Apply the conformal ADM flux law to a compactly supported Ricci variation. The realized masses would have nonzero first derivative at their minimum.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.zero_mass_ricci_flat_by_first_variation (Q : Type) [m : MetricSpace Q] [ch : ChartedSpace ADMPoint Q] [sm : IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [rb : RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [sr : IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [rm : IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] [cm : CompleteSpace Q] [cn : ConnectedSpace Q]
    [sc : SecondCountableTopology Q]
    (hend : HasScalarFlatZeroADMEnd Q)
    (nonnegative : ∀ m : ℝ, IsScalarFlatADMMass m → 0 ≤ m) : RicciFlatInADMCharts Q := by sorry
