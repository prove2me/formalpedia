-- Prove2me | Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_coordinates
-- name    : NewtonianLipschitz.euclideanRadius_eq_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:20:21.440545+00:00
-- url     : https://prove2.me/theorems/5d77e23b-a3b6-4a6f-9946-5ade71c62806
-- title:
--   Newtonian Lipschitz: euclidean Radius eq coordinates
-- statement:
--   The chosen coordinate expression for the physical radius.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Basic.lean#L25-L27
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Basic.lean#L25-L27

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_Basic
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.euclideanRadius_eq_coordinates (x : Vec3) :
    euclideanRadius x = Real.sqrt (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by sorry
