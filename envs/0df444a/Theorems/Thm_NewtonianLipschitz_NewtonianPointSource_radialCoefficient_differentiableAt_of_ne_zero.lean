-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_radialCoefficient_differentiableAt_of_ne_zero
-- name    : NewtonianLipschitz.NewtonianPointSource.radialCoefficient_differentiableAt_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:18.030378+00:00
-- url     : https://prove2.me/theorems/6a924007-8306-42c4-b387-552328c9823e
-- title:
--   Newtonian Point Source: radial Coefficient differentiable At of ne zero
-- statement:
--   The radial-prefactor differentiability premise is
--   unconditionally available at any noncolliding source separation.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Derivative.lean#L85-L88
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Derivative.lean#L85-L88

module
public import Definitions.Def_NewtonianLipschitz_Smoothness
public import Definitions.Def_NewtonianLipschitz_Norms
public import Definitions.Def_NewtonianLipschitz_Derivative
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.radialCoefficient_differentiableAt_of_ne_zero
    (c : NewtonianPointSource) (x : Vec3) (hx : x ≠ 0) :
    DifferentiableAt ℝ c.radialCoefficient x := by sorry
