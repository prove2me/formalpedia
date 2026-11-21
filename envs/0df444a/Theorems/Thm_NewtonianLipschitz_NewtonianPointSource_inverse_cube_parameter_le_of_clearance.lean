-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_inverse_cube_parameter_le_of_clearance
-- name    : NewtonianLipschitz.NewtonianPointSource.inverse_cube_parameter_le_of_clearance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:25:47.539633+00:00
-- url     : https://prove2.me/theorems/249f1a2a-41e4-46fc-a95a-ffce8cf09bca
-- title:
--   Newtonian Point Source: inverse cube parameter le of clearance
-- statement:
--   The inverse-cube coefficient `μ/r³` of the exact Newtonian
--   acceleration is bounded by `M/d³` when `r ≥ d > 0`.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/BaselineBounds.lean#L40-L47
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/BaselineBounds.lean#L40-L47

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.inverse_cube_parameter_le_of_clearance
    (c : NewtonianPointSource) (x : Vec3) (d M : ℝ)
    (hd : 0 < d)
    (hclear : d ≤ euclideanRadius x)
    (hM : c.gravitationalParameter ≤ M) :
    c.gravitationalParameter / euclideanRadius x ^ 3 ≤
      M / d ^ 3 := by sorry
