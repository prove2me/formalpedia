-- Prove2me | Theorems.Thm_NewtonianLipschitz_cartesian_opposite_safe_sides_separated
-- name    : NewtonianLipschitz.cartesian_opposite_safe_sides_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:50:18.531461+00:00
-- url     : https://prove2.me/theorems/5881c95a-7d7a-4849-8504-aecc39bd27d3
-- title:
--   Newtonian Lipschitz: cartesian opposite safe sides separated
-- statement:
--   If the same coordinate is safe on opposite sides of
--   the cube for x and y, their Cartesian separation is at
--   least d, so R038 applies.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/SafePlaneReduction.lean#L135-L151
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/SafePlaneReduction.lean#L135-L151

module
public import Definitions.Def_NewtonianLipschitz_ConditionalFiniteSource
public import Definitions.Def_NewtonianLipschitz_TangentialAlgebra
public import Definitions.Def_NewtonianLipschitz_SafePlaneReduction
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.cartesian_opposite_safe_sides_separated
    (x y : Vec3) (d : ℝ) (hd : 0 < d)
    (i : Fin 3)
    (hpos : d ≤ x i) (hneg : y i ≤ -d) :
    d ≤ ‖x - y‖ := by sorry
