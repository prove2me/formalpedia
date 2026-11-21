-- Prove2me | Theorems.Thm_NewtonianLipschitz_cartesianPositiveSafeHalfspace_clearance
-- name    : NewtonianLipschitz.cartesianPositiveSafeHalfspace_clearance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:45:56.194293+00:00
-- url     : https://prove2.me/theorems/e1b33d89-7b73-4328-9256-5ffcea8e2d45
-- title:
--   Newtonian Lipschitz: cartesian Positive Safe Halfspace clearance
-- statement:
--   Every point in a positive coordinate supporting halfspace
--   has at least d Cartesian norm.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CommonSafeFace.lean#L38-L43
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CommonSafeFace.lean#L38-L43

module
public import Definitions.Def_NewtonianLipschitz_LongSeparation
public import Definitions.Def_NewtonianLipschitz_CommonSafeFace
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.cartesianPositiveSafeHalfspace_clearance (i : Fin 3) (d : ℝ) :
    ∀ z : Vec3, d ≤ z i → d ≤ ‖z‖ := by sorry
