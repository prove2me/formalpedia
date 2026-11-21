-- Prove2me | Theorems.Thm_NewtonianLipschitz_euclideanRadius_smul
-- name    : NewtonianLipschitz.euclideanRadius_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:34:32.10509+00:00
-- url     : https://prove2.me/theorems/02d0d369-9c22-40ef-96fb-5a2926e35db1
-- title:
--   Newtonian Lipschitz: euclidean Radius smul
-- statement:
--   The physical Euclidean radius scales like an ordinary norm.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSymmetries.lean#L76-L82
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSymmetries.lean#L76-L82

module
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.euclideanRadius_smul (c : ℝ) (x : Vec3) :
    euclideanRadius (c • x) = |c| * euclideanRadius x := by sorry
