-- Prove2me | Theorems.Thm_NewtonianLipschitz_cartesian_exists_signed_safe_coordinate
-- name    : NewtonianLipschitz.cartesian_exists_signed_safe_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:49:24.854894+00:00
-- url     : https://prove2.me/theorems/52d151e9-b77e-4967-841d-75c838286935
-- title:
--   Newtonian Lipschitz: cartesian exists signed safe coordinate
-- statement:
--   Positive clearance in the Cartesian maximum norm
--   means that at least one signed coordinate is safe.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/SafePlaneReduction.lean#L42-L60
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/SafePlaneReduction.lean#L42-L60

module
public import Definitions.Def_NewtonianLipschitz_ConditionalFiniteSource
public import Definitions.Def_NewtonianLipschitz_TangentialAlgebra
public import Definitions.Def_NewtonianLipschitz_SafePlaneReduction
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.cartesian_exists_signed_safe_coordinate
    (x : Vec3) (d : ℝ) (hx : d ≤ ‖x‖) :
    ∃ i : Fin 3, d ≤ x i ∨ x i ≤ -d := by sorry
