-- Prove2me | Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
-- name    : NewtonianLipschitz.ofLp_toPhysicalVec3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:20:14.007184+00:00
-- url     : https://prove2.me/theorems/2a04fd4c-4d19-428a-ad86-18689fe97360
-- title:
--   Newtonian Lipschitz: of Lp to Physical Vec3
-- statement:
--   The inverse conversion returns the original Cartesian vector.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Basic.lean#L58-L60
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Basic.lean#L58-L60

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_Basic
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.ofLp_toPhysicalVec3 (q : Vec3) :
    WithLp.ofLp (toPhysicalVec3 q) = q := by sorry

attribute [defeq] NewtonianLipschitz.ofLp_toPhysicalVec3
