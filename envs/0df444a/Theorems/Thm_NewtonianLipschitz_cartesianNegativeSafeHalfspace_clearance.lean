-- Prove2me | Theorems.Thm_NewtonianLipschitz_cartesianNegativeSafeHalfspace_clearance
-- name    : NewtonianLipschitz.cartesianNegativeSafeHalfspace_clearance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:46:11.058612+00:00
-- url     : https://prove2.me/theorems/ee0b57dc-1a05-4cff-90cd-b0629579494e
-- title:
--   Newtonian Lipschitz: cartesian Negative Safe Halfspace clearance
-- statement:
--   Every point in a negative coordinate supporting halfspace
--   has at least d Cartesian norm.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CommonSafeFace.lean#L55-L61
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CommonSafeFace.lean#L55-L61

module
public import Definitions.Def_NewtonianLipschitz_LongSeparation
public import Definitions.Def_NewtonianLipschitz_CommonSafeFace
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.cartesianNegativeSafeHalfspace_clearance (i : Fin 3) (d : ℝ) :
    ∀ z : Vec3, z i ≤ -d → d ≤ ‖z‖ := by sorry
