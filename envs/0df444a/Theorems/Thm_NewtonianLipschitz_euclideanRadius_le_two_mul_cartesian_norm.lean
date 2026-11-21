-- Prove2me | Theorems.Thm_NewtonianLipschitz_euclideanRadius_le_two_mul_cartesian_norm
-- name    : NewtonianLipschitz.euclideanRadius_le_two_mul_cartesian_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:49.959021+00:00
-- url     : https://prove2.me/theorems/581c11a2-a109-4877-b4e7-2b1ef5395354
-- title:
--   Newtonian Lipschitz: euclidean Radius le two mul cartesian norm
-- statement:
--   Conservative but sharper bound between the physical radius and
--   the Cartesian supremum norm.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Norms.lean#L74-L90
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Norms.lean#L74-L90

module
public import Definitions.Def_NewtonianLipschitz_Basic
public import Definitions.Def_NewtonianLipschitz_Norms
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.euclideanRadius_le_two_mul_cartesian_norm (x : Vec3) :
    euclideanRadius x ≤ 2 * ‖x‖ := by sorry
