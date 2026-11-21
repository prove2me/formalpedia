-- Prove2me | Theorems.Thm_NewtonianLipschitz_cartesianPositiveSafeHalfspace_convex
-- name    : NewtonianLipschitz.cartesianPositiveSafeHalfspace_convex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:45:47.291882+00:00
-- url     : https://prove2.me/theorems/6662f11c-94d0-4159-8b4d-9808227c6cf2
-- title:
--   Newtonian Lipschitz: cartesian Positive Safe Halfspace convex
-- statement:
--   A coordinate supporting halfspace on the positive side of
--   the forbidden Cartesian cube is convex.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CommonSafeFace.lean#L29-L34
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CommonSafeFace.lean#L29-L34

module
public import Definitions.Def_NewtonianLipschitz_LongSeparation
public import Definitions.Def_NewtonianLipschitz_CommonSafeFace
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.cartesianPositiveSafeHalfspace_convex (i : Fin 3) (d : ℝ) :
    Convex ℝ {z : Vec3 | d ≤ z i} := by sorry
