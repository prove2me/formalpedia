-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_sub_le_fiveFourth_safePlane
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_fiveFourth_safePlane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:53:17.86402+00:00
-- url     : https://prove2.me/theorems/65e45135-b69b-4544-b670-ab9e87ff99fa
-- title:
--   Newtonian Point Source: acceleration Field norm sub le five Fourth safe Plane
-- statement:
--   A 5/4 bound on the actual Newtonian force difference
--   between any two endpoints with a fixed signed-safe coordinate.
--   The segment remains safe, and the estimate is obtained by
--   integrating R046's genuine tangent derivative.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/SafePlaneFiniteDifference.lean#L29-L108
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/SafePlaneFiniteDifference.lean#L29-L108

module
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialAllAxes
public import Definitions.Def_NewtonianLipschitz_SafePlaneFiniteDifference
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_fiveFourth_safePlane
    (c : NewtonianPointSource) (x y : Vec3) (d : ℝ) (i : Fin 3)
    (hd : 0 < d) (hxy : x i = y i)
    (hsafe : d ≤ x i ∨ x i ≤ -d) :
    ‖c.accelerationField x - c.accelerationField y‖ ≤
      ((1 / d ^ 3) *
        (c.gravitationalParameter * (5 / 4 : ℝ))) * ‖x - y‖ := by sorry
