-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_eq_radialCoefficient_smul
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_eq_radialCoefficient_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:59.499709+00:00
-- url     : https://prove2.me/theorems/cc86e3dc-c49b-4f19-b4dc-b60e27c86adc
-- title:
--   Newtonian Point Source: acceleration Field eq radial Coefficient smul
-- statement:
--   Exact acceleration factorization into scalar and vector.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Derivative.lean#L25-L29
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Derivative.lean#L25-L29

module
public import Definitions.Def_NewtonianLipschitz_Smoothness
public import Definitions.Def_NewtonianLipschitz_Norms
public import Definitions.Def_NewtonianLipschitz_Derivative
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_eq_radialCoefficient_smul
    (c : NewtonianPointSource) (x : Vec3) :
    c.accelerationField x = c.radialCoefficient x • x := by sorry
