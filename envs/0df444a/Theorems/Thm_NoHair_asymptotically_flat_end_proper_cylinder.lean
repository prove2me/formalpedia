-- Prove2me | Theorems.Thm_NoHair_asymptotically_flat_end_proper_cylinder
-- name    : NoHair.asymptotically_flat_end_proper_cylinder
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T11:07:02.611362+00:00
-- url     : https://prove2.me/theorems/f69de764-6908-4b39-b20f-f400ec80dead
-- title:
--   Proper cylindrical parametrization at spatial infinity
-- statement:
--   A far asymptotically flat end admits an open spherical cylinder parametrization whose positive tails eventually avoid every compact subset of the complete manifold.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.asymptotically_flat_end_proper_cylinder (Q : Type) [m : MetricSpace Q] [ch : ChartedSpace ADMPoint Q] [sm : IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [rb : RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [sr : IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [rm : IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] [cm : CompleteSpace Q] [cn : ConnectedSpace Q]
    [sc : SecondCountableTopology Q]
    (hend : HasScalarFlatZeroADMEnd Q) :
    ∃ e : ADMSphere × ℝ → Q, Topology.IsOpenEmbedding e ∧
      ∀ K : Set Q, IsCompact K → ∃ T : ℝ, ∀ n : ADMSphere, ∀ t : ℝ, T<t → e (n,t) ∉ K := by sorry
