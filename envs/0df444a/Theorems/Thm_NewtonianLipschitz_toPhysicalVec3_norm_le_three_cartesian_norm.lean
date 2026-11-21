-- Prove2me | Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_norm_le_three_cartesian_norm
-- name    : NewtonianLipschitz.toPhysicalVec3_norm_le_three_cartesian_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:47.687758+00:00
-- url     : https://prove2.me/theorems/84d369b2-a87a-439b-a174-c23f82da8bb8
-- title:
--   Newtonian Lipschitz: to Physical Vec3 norm le three cartesian norm
-- statement:
--   A corollary for the true physical vector, expressed in the exact
--   norm that appears in the Newtonian derivative.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Norms.lean#L59-L62
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Norms.lean#L59-L62

module
public import Definitions.Def_NewtonianLipschitz_Basic
public import Definitions.Def_NewtonianLipschitz_Norms
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.toPhysicalVec3_norm_le_three_cartesian_norm (x : Vec3) :
    ‖toPhysicalVec3 x‖ ≤ 3 * ‖x‖ := by sorry
