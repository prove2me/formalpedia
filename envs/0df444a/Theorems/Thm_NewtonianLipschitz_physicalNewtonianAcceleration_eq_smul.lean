-- Prove2me | Theorems.Thm_NewtonianLipschitz_physicalNewtonianAcceleration_eq_smul
-- name    : NewtonianLipschitz.physicalNewtonianAcceleration_eq_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:26.792465+00:00
-- url     : https://prove2.me/theorems/e7a3352d-dbb5-402b-a3c0-78988ace6457
-- title:
--   Newtonian Lipschitz: physical Newtonian Acceleration eq smul
-- statement:
--   Public scalar-multiple form of physical Newtonian acceleration for
--   linking Euclidean regularity to the original Cartesian dynamics.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Smoothness.lean#L24-L26
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Smoothness.lean#L24-L26

module
public import Definitions.Def_NewtonianLipschitz_Field
public import Definitions.Def_NewtonianLipschitz_Smoothness
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.physicalNewtonianAcceleration_eq_smul (μ : ℝ) (q : PhysicalVec3) :
    physicalNewtonianAcceleration μ q = (-(μ) / ‖q‖ ^ 3) • q := by sorry
