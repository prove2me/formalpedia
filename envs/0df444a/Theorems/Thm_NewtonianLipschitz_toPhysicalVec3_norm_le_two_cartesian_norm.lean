-- Prove2me | Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_norm_le_two_cartesian_norm
-- name    : NewtonianLipschitz.toPhysicalVec3_norm_le_two_cartesian_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:50.131195+00:00
-- url     : https://prove2.me/theorems/9aff0ffd-84ee-4660-be86-f11617fb12bd
-- title:
--   Newtonian Lipschitz: to Physical Vec3 norm le two cartesian norm
-- statement:
--   Physical norm bound with coefficient two.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Norms.lean#L93-L96
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Norms.lean#L93-L96

module
public import Definitions.Def_NewtonianLipschitz_Basic
public import Definitions.Def_NewtonianLipschitz_Norms
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.toPhysicalVec3_norm_le_two_cartesian_norm (x : Vec3) :
    ‖toPhysicalVec3 x‖ ≤ 2 * ‖x‖ := by sorry
