-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianNumerator_coordinateAbs
-- name    : NewtonianLipschitz.newtonianJacobianNumerator_coordinateAbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:34:23.277567+00:00
-- url     : https://prove2.me/theorems/5def88b3-28ed-42a4-b537-262a100d01a1
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Numerator coordinate Abs
-- statement:
--   The elementary numerator of the physical matrix has an
--   absolute value invariant under coordinatewise sign changes.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSymmetries.lean#L37-L51
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSymmetries.lean#L37-L51

module
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianNumerator_coordinateAbs (x : Vec3)
    (i j : Fin 3) :
    |3 * coordinateAbs x i * coordinateAbs x j -
      euclideanRadius x ^ 2 * (if i = j then 1 else 0)| =
    |3 * x i * x j -
      euclideanRadius x ^ 2 * (if i = j then 1 else 0)| := by sorry
