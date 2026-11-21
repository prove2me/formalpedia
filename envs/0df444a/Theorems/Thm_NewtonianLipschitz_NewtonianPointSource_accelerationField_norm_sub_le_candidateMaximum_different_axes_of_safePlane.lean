-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_sub_le_candidateMaximum_different_axes_of_safePlane
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_candidateMaximum_different_axes_of_safePlane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:49:42.5595+00:00
-- url     : https://prove2.me/theorems/fdbd33b5-0a27-4d49-ab1c-9b2685e589ec
-- title:
--   Newtonian Point Source: acceleration Field norm sub le candidate Maximum different axes of safe Plane
-- statement:
--   Conditional improvement of R040: if the physical
--   5/4 estimate is available on every fixed safe plane,
--   a two-hop connection between different active axes
--   has factor 5/2, strictly smaller than C3.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/SafePlaneReduction.lean#L66-L130
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/SafePlaneReduction.lean#L66-L130

module
public import Definitions.Def_NewtonianLipschitz_ConditionalFiniteSource
public import Definitions.Def_NewtonianLipschitz_TangentialAlgebra
public import Definitions.Def_NewtonianLipschitz_SafePlaneReduction
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_candidateMaximum_different_axes_of_safePlane
    (hPlane : oneSourceSafePlaneFiveFourthBound)
    (c : NewtonianPointSource) (x y : Vec3) (d : ℝ)
    (hd : 0 < d) (i j : Fin 3) (hij : i ≠ j)
    (hxi : d ≤ x i ∨ x i ≤ -d)
    (hyj : d ≤ y j ∨ y j ≤ -d) :
    ‖c.accelerationField x - c.accelerationField y‖ ≤
      ((1 / d ^ 3) *
        (c.gravitationalParameter * candidateMaximum)) * ‖x - y‖ := by sorry
