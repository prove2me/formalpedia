-- Prove2me | Theorems.Thm_NewtonianLipschitz_cartesian_norm_eq_max_abs
-- name    : NewtonianLipschitz.cartesian_norm_eq_max_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:42.654976+00:00
-- url     : https://prove2.me/theorems/ff3829f2-feb6-4b6d-8072-4eb7ceb6df14
-- title:
--   Newtonian Lipschitz: cartesian norm eq max abs
-- statement:
--   The norm on Vec3 is exactly the largest absolute value
--   of its three Cartesian coordinates.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianCartesianBound.lean#L23-L26
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianCartesianBound.lean#L23-L26

module
public import Definitions.Def_NewtonianLipschitz_JacobianSignedBounds
public import Definitions.Def_NewtonianLipschitz_JacobianCartesianBound
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.cartesian_norm_eq_max_abs (x : Vec3) :
    ‖x‖ = max (|x 0|) (max (|x 1|) (|x 2|)) := by sorry
