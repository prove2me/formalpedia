-- Prove2me | Theorems.Thm_NoHair_euclidean_cover_lifts_af_exterior
-- name    : NoHair.euclidean_cover_lifts_af_exterior
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:58:54.693057+00:00
-- url     : https://prove2.me/theorems/6829e9c1-fbbc-47b3-8991-bdb12503cc5a
-- title:
--   Lift an asymptotically flat three-dimensional end to an exterior sheet
-- statement:
--   Lift a sufficiently far simply connected exterior $S^2\times(R,\infty)$ to a sheet in the Euclidean covering space. Its frontier is the compact lift of a truncating sphere in a slightly larger exterior chart. Its points escape every compact set, as seen by projecting and using the asymptotic metric lower bound.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.euclidean_cover_lifts_af_exterior (Q : Type) [m : MetricSpace Q] [ch : ChartedSpace ADMPoint Q] [sm : IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [rb : RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [sr : IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [rm : IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] [cm : CompleteSpace Q] [cn : ConnectedSpace Q]
    [sc : SecondCountableTopology Q]
    (hend : HasScalarFlatZeroADMEnd Q) (p : ADMPoint → Q) (cover : IsCoveringMap p) :
    ∃ U : Set ADMPoint, IsOpen U ∧ ¬ Bornology.IsBounded U ∧ IsCompact (frontier U) ∧ Set.InjOn p U := by sorry
