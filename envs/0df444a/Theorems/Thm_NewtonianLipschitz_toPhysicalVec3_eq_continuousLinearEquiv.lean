-- Prove2me | Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_eq_continuousLinearEquiv
-- name    : NewtonianLipschitz.toPhysicalVec3_eq_continuousLinearEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:20:17.464891+00:00
-- url     : https://prove2.me/theorems/c8ffb50a-ac63-4b9f-bf4f-d1002b513c84
-- title:
--   Newtonian Lipschitz: to Physical Vec3 eq continuous Linear Equiv
-- statement:
--   The physical coordinate conversion is the canonical continuous
--   linear equivalence, enabling regularity transfer without unfolding.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Basic.lean#L52-L55
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Basic.lean#L52-L55

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_Basic
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.toPhysicalVec3_eq_continuousLinearEquiv (q : Vec3) :
    toPhysicalVec3 q =
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm) q := by sorry
