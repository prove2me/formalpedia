-- Prove2me | Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_physical_norm
-- name    : NewtonianLipschitz.euclideanRadius_eq_physical_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:20:11.421094+00:00
-- url     : https://prove2.me/theorems/7947d990-6829-4117-aecb-1be9219e9620
-- title:
--   Newtonian Lipschitz: euclidean Radius eq physical norm
-- statement:
--   The Newtonian Lipschitz construction uses the euclidean Radius eq physical norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Basic.lean#L62-L65
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Basic.lean#L62-L65

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_Basic
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.euclideanRadius_eq_physical_norm (q : Vec3) :
    euclideanRadius q = ‖toPhysicalVec3 q‖ := by sorry
