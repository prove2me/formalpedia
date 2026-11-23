-- Prove2me | Theorems.Thm_NoHair_asymptotically_flat_spatial_coordinates_escape
-- name    : NoHair.asymptotically_flat_spatial_coordinates_escape
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T11:11:26.313842+00:00
-- url     : https://prove2.me/theorems/fbf8348c-9dc0-4e21-8e56-aa44af057d7b
-- title:
--   Asymptotically flat spatial coordinates escape every compact set
-- statement:
--   The lower metric bound on the given end controls the inverse differential. Scale and translate a Euclidean bump of fixed shape about a distant coordinate point, with height and support radius proportional to its coordinate radius. Transplant it to the manifold and extend it by zero. The resulting functions have a common Lipschitz constant, which forces physical distances from a fixed point to grow at least linearly with coordinate radius.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.asymptotically_flat_spatial_coordinates_escape (Q : Type) [m : MetricSpace Q] [ch : ChartedSpace ADMPoint Q] [sm : IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [rb : RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [sr : IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [rm : IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] [cm : CompleteSpace Q] [cn : ConnectedSpace Q]
    [sc : SecondCountableTopology Q]
    (hend : HasScalarFlatZeroADMEnd Q) :
    ∃ (R : ℝ) (e : OpenPartialHomeomorph ADMPoint Q), 0<R ∧ e.source={x | R<‖x‖} ∧
      ∀ K : Set Q, IsCompact K → ∃ T : ℝ, ∀ x : ADMPoint, T<‖x‖ → e x ∉ K := by sorry
