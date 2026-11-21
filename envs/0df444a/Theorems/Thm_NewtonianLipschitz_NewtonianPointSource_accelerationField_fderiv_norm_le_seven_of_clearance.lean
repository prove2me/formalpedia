-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_norm_le_seven_of_clearance
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_norm_le_seven_of_clearance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:37:08.385071+00:00
-- url     : https://prove2.me/theorems/86c8aae6-d05b-4a04-9f93-caf90fd44ee7
-- title:
--   Newtonian Point Source: acceleration Field fderiv norm le seven of clearance
-- statement:
--   Derived dimensionless coefficient 7 for the exact Newtonian
--   Fréchet derivative, assuming positive Euclidean clearance.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ImprovedBounds.lean#L22-L102
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ImprovedBounds.lean#L22-L102

module
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
public import Definitions.Def_NewtonianLipschitz_ImprovedBounds
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_norm_le_seven_of_clearance
    (c : NewtonianPointSource) (x h : Vec3) (d M : ℝ)
    (hx : x ≠ 0) (hd : 0 < d)
    (hclear : d ≤ euclideanRadius x)
    (hM : c.gravitationalParameter ≤ M) :
    ‖(fderiv ℝ c.accelerationField x) h‖ ≤
      (7 * M / d ^ 3) * ‖h‖ := by sorry
