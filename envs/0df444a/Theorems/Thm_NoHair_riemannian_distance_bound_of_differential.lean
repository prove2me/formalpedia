-- Prove2me | Theorems.Thm_NoHair_riemannian_distance_bound_of_differential
-- name    : NoHair.riemannian_distance_bound_of_differential
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T11:13:00.779736+00:00
-- url     : https://prove2.me/theorems/352a4f62-1d0b-46ca-9d2d-6ef8dcdf6280
-- title:
--   Distance bound from a uniform differential bound on a Riemannian manifold
-- statement:
--   A real-valued smooth function with differential bounded by $K$ is globally $K$-Lipschitz for the intrinsic Riemannian distance. Apply the chain rule along paths and take the infimum of their lengths.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.riemannian_distance_bound_of_differential (Q : Type) [MetricSpace Q] [ChartedSpace ADMPoint Q] [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] (f : Q → ℝ)
    (hf : ContMDiff 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ℝ) 1 f) (K : NNReal) (hk : 0 < K)
    (bound : ∀ q, ∀ v : TangentSpace 𝓘(ℝ,ADMPoint) q,
      ‖mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ℝ) f q v‖ ≤ K * ‖v‖) : LipschitzWith K f := by sorry
