-- Prove2me | Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
-- name    : NewtonianLipschitz.toPhysicalVec3_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:20:17.99523+00:00
-- url     : https://prove2.me/theorems/a2de470c-cc9e-4503-9d4c-4c38639d273d
-- title:
--   Newtonian Lipschitz: to Physical Vec3 apply
-- statement:
--   Cartesian coordinates are unchanged componentwise by the
--   conversion to the Euclidean-normed physical vector representation.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Basic.lean#L46-L48
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Basic.lean#L46-L48

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_Basic
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.toPhysicalVec3_apply (q : Vec3) (i : Fin 3) :
    toPhysicalVec3 q i = q i := by sorry

attribute [defeq] NewtonianLipschitz.toPhysicalVec3_apply
