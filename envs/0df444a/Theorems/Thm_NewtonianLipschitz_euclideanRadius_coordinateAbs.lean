-- Prove2me | Theorems.Thm_NewtonianLipschitz_euclideanRadius_coordinateAbs
-- name    : NewtonianLipschitz.euclideanRadius_coordinateAbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:34:00.43483+00:00
-- url     : https://prove2.me/theorems/3dd429cf-508d-47d5-a5dd-0ec84a8fbab1
-- title:
--   Newtonian Lipschitz: euclidean Radius coordinate Abs
-- statement:
--   Taking absolute values componentwise preserves physical radius.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSymmetries.lean#L29-L33
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSymmetries.lean#L29-L33

module
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.euclideanRadius_coordinateAbs (x : Vec3) :
    euclideanRadius (coordinateAbs x) = euclideanRadius x := by sorry
