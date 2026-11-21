-- Prove2me | Theorems.Thm_NewtonianLipschitz_euclideanRadius_le_three_mul_cartesian_norm
-- name    : NewtonianLipschitz.euclideanRadius_le_three_mul_cartesian_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:44.528264+00:00
-- url     : https://prove2.me/theorems/23a44d57-8576-4151-8081-af36b806fbcd
-- title:
--   Newtonian Lipschitz: euclidean Radius le three mul cartesian norm
-- statement:
--   The Newtonian Lipschitz construction uses the euclidean Radius le three mul cartesian norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Norms.lean#L39-L55
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Norms.lean#L39-L55

module
public import Definitions.Def_NewtonianLipschitz_Basic
public import Definitions.Def_NewtonianLipschitz_Norms
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.euclideanRadius_le_three_mul_cartesian_norm (x : Vec3) :
    euclideanRadius x ≤ 3 * ‖x‖ := by sorry
