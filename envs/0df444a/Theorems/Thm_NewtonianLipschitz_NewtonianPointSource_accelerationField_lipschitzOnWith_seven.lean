-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_lipschitzOnWith_seven
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_lipschitzOnWith_seven
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:37:39.563582+00:00
-- url     : https://prove2.me/theorems/9964ca03-c11d-41de-9825-62fa3539a4f6
-- title:
--   Newtonian Point Source: acceleration Field lipschitz On With seven
-- statement:
--   Fully derived, nonoptimal convex-domain Lipschitz certificate
--   for the exact Newtonian force.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConvexImproved.lean#L37-L74
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConvexImproved.lean#L37-L74

module
public import Definitions.Def_NewtonianLipschitz_ImprovedBounds
public import Definitions.Def_NewtonianLipschitz_Clearance
public import Definitions.Def_NewtonianLipschitz_ConvexImproved
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_lipschitzOnWith_seven
    (c : NewtonianPointSource) (positions : Set Vec3)
    (hconvex : Convex ℝ positions)
    (d : ℝ) (M : ℝ≥0) (hd : 0 < d)
    (hclear : ∀ x ∈ positions, d ≤ euclideanRadius x)
    (hM : c.gravitationalParameter ≤ (M : ℝ)) :
    LipschitzOnWith
      (NewtonianPointSource.sevenLipschitzCoefficient d M hd)
      c.accelerationField positions := by sorry
