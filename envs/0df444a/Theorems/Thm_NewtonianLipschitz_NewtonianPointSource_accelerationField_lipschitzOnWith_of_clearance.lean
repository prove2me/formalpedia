-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_lipschitzOnWith_of_clearance
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_lipschitzOnWith_of_clearance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:37:15.850544+00:00
-- url     : https://prove2.me/theorems/ae3e3220-a0e2-4f3b-99c9-466f40a57601
-- title:
--   Newtonian Point Source: acceleration Field lipschitz On With of clearance
-- statement:
--   Mean-value transfer: an *explicit derived* bound on the actual
--   inverse-cube field's Fréchet derivative yields a Lipschitz certificate
--   on any convex, uniformly noncolliding spatial domain. This avoids
--   assuming an independent unit-field Lipschitz certificate.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConvexBaseline.lean#L57-L91
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConvexBaseline.lean#L57-L91

module
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
public import Definitions.Def_NewtonianLipschitz_Clearance
public import Definitions.Def_NewtonianLipschitz_ConvexBaseline
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_lipschitzOnWith_of_clearance
    (c : NewtonianPointSource) (positions : Set Vec3)
    (hconvex : Convex ℝ positions)
    (d : ℝ) (M : ℝ≥0) (hd : 0 < d)
    (hclear : ∀ x ∈ positions, d ≤ euclideanRadius x)
    (hM : c.gravitationalParameter ≤ (M : ℝ)) :
    LipschitzOnWith
      (NewtonianPointSource.clearanceLipschitzCoefficient d M hd)
      c.accelerationField positions := by sorry
