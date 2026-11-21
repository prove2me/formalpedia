-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_sub_le_candidateMaximum_convex
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_candidateMaximum_convex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:36:30.902949+00:00
-- url     : https://prove2.me/theorems/8edc060b-8ea4-4c91-8475-0b81fd33ce5a
-- title:
--   Newtonian Point Source: acceleration Field norm sub le candidate Maximum convex
-- statement:
--   The actual Newtonian acceleration field obeys the exact
--   candidate coefficient on every convex set with positive
--   Cartesian clearance from the source. The conclusion bounds
--   the finite difference between any two points of that set.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConvexSharp.lean#L28-L56
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConvexSharp.lean#L28-L56

module
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorWitness
public import Definitions.Def_NewtonianLipschitz_ConvexBaseline
public import Definitions.Def_NewtonianLipschitz_ConvexSharp
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_candidateMaximum_convex
    (c : NewtonianPointSource)
    (positions : Set Vec3) (hconvex : Convex ℝ positions)
    (d : ℝ) (hd : 0 < d)
    (hclear : ∀ z ∈ positions, d ≤ ‖z‖)
    (x y : Vec3) (hx : x ∈ positions) (hy : y ∈ positions) :
    ‖c.accelerationField x - c.accelerationField y‖ ≤
      ((1 / d ^ 3) * (c.gravitationalParameter * candidateMaximum)) *
        ‖x - y‖ := by sorry
