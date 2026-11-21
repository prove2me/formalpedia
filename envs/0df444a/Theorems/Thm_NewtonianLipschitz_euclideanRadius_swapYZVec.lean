-- Prove2me | Theorems.Thm_NewtonianLipschitz_euclideanRadius_swapYZVec
-- name    : NewtonianLipschitz.euclideanRadius_swapYZVec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:34:34.537391+00:00
-- url     : https://prove2.me/theorems/a9cfcd66-b9a9-47db-9487-2b5cc1f2cd3e
-- title:
--   Newtonian Lipschitz: euclidean Radius swap YZVec
-- statement:
--   The physical source radius is invariant under swapping Y and Z.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L92-L98
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L92-L98

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.euclideanRadius_swapYZVec (x : Vec3) :
    euclideanRadius (swapYZVec x) = euclideanRadius x := by sorry
