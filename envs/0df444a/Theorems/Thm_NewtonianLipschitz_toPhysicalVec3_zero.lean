-- Prove2me | Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
-- name    : NewtonianLipschitz.toPhysicalVec3_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:20:12.91733+00:00
-- url     : https://prove2.me/theorems/669528e8-d64a-42f2-aa7d-1b4f24c17850
-- title:
--   Newtonian Lipschitz: to Physical Vec3 zero
-- statement:
--   The Cartesian-to-physical Euclidean map preserves the zero vector.
--   This also makes the property available to downstream modules, where
--   the body of `toPhysicalVec3` is deliberately opaque.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Basic.lean#L41-L42
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Basic.lean#L41-L42

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_Basic
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.toPhysicalVec3_zero : toPhysicalVec3 (0 : Vec3) = 0 := by sorry

attribute [defeq] NewtonianLipschitz.toPhysicalVec3_zero
