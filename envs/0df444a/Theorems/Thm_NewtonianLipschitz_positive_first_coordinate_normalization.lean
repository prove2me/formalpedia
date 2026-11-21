-- Prove2me | Theorems.Thm_NewtonianLipschitz_positive_first_coordinate_normalization
-- name    : NewtonianLipschitz.positive_first_coordinate_normalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:18.635814+00:00
-- url     : https://prove2.me/theorems/2e5eab51-db4b-4938-ba3d-dfbf4725d70e
-- title:
--   Newtonian Lipschitz: positive first coordinate normalization
-- statement:
--   If X is positive, a nonnegative displacement is exactly
--   its X coordinate times a vector whose first coordinate is one.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianNormalization.lean#L43-L65
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianNormalization.lean#L43-L65

module
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
public import Definitions.Def_NewtonianLipschitz_JacobianNormalization
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.positive_first_coordinate_normalization
    (x : Vec3) (hx0 : 0 < x 0) :
    (x 0) • normalizedVector (x 1 / x 0) (x 2 / x 0) = x := by sorry
