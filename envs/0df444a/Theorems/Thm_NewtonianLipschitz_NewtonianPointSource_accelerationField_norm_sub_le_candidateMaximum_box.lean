-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_sub_le_candidateMaximum_box
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_candidateMaximum_box
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:55:38.053397+00:00
-- url     : https://prove2.me/theorems/b9a52002-3329-4d65-b8a9-3c6f6c7e07c7
-- title:
--   Newtonian Point Source: acceleration Field norm sub le candidate Maximum box
-- statement:
--   The optimal candidate C3 bounds every pair of Newtonian
--   accelerations inside an explicitly certified Cartesian box.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CartesianBoxSharp.lean#L43-L56
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CartesianBoxSharp.lean#L43-L56

module
public import Definitions.Def_NewtonianLipschitz_ConvexSharp
public import Definitions.Def_NewtonianLipschitz_CartesianBoxSharp
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_candidateMaximum_box
    (c : NewtonianPointSource)
    (anchor : Vec3) (ρ d : ℝ)
    (hd : 0 < d) (hmargin : d + ρ ≤ dist anchor (0 : Vec3))
    (x y : Vec3)
    (hx : x ∈ Metric.ball anchor ρ)
    (hy : y ∈ Metric.ball anchor ρ) :
    ‖c.accelerationField x - c.accelerationField y‖ ≤
      ((1 / d ^ 3) * (c.gravitationalParameter * candidateMaximum)) *
        ‖x - y‖ := by sorry
