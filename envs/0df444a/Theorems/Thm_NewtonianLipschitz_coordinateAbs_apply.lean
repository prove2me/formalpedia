-- Prove2me | Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
-- name    : NewtonianLipschitz.coordinateAbs_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:25:28.070168+00:00
-- url     : https://prove2.me/theorems/baa49e43-12f7-44cc-ab18-c7e3728d91c6
-- title:
--   Newtonian Lipschitz: coordinate Abs apply
-- statement:
--   The Newtonian Lipschitz construction uses the coordinate Abs apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSymmetries.lean#L24-L26
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSymmetries.lean#L24-L26

module
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.coordinateAbs_apply (x : Vec3) (i : Fin 3) :
    coordinateAbs x i = |x i| := by sorry

attribute [defeq] NewtonianLipschitz.coordinateAbs_apply
