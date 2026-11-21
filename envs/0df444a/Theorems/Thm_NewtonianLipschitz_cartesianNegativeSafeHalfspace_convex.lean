-- Prove2me | Theorems.Thm_NewtonianLipschitz_cartesianNegativeSafeHalfspace_convex
-- name    : NewtonianLipschitz.cartesianNegativeSafeHalfspace_convex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:46:02.042309+00:00
-- url     : https://prove2.me/theorems/5d529950-2541-48a1-9282-a13998b52ef2
-- title:
--   Newtonian Lipschitz: cartesian Negative Safe Halfspace convex
-- statement:
--   A negative coordinate supporting halfspace is convex.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CommonSafeFace.lean#L46-L51
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CommonSafeFace.lean#L46-L51

module
public import Definitions.Def_NewtonianLipschitz_LongSeparation
public import Definitions.Def_NewtonianLipschitz_CommonSafeFace
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.cartesianNegativeSafeHalfspace_convex (i : Fin 3) (d : ℝ) :
    Convex ℝ {z : Vec3 | z i ≤ -d} := by sorry
