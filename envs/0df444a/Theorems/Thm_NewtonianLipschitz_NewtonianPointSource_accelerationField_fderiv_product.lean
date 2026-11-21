-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_product
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:57.398685+00:00
-- url     : https://prove2.me/theorems/72422ec0-b815-408a-9afd-d5e3850c2db1
-- title:
--   Newtonian Point Source: acceleration Field fderiv product
-- statement:
--   Conditional product-rule factorization of the TRUE
--   Fréchet derivative. The scalar differentiability assumption is
--   supplied rather than proved from noncollision.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Derivative.lean#L34-L52
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Derivative.lean#L34-L52

module
public import Definitions.Def_NewtonianLipschitz_Smoothness
public import Definitions.Def_NewtonianLipschitz_Norms
public import Definitions.Def_NewtonianLipschitz_Derivative
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_product
    (c : NewtonianPointSource) (x : Vec3)
    (hcoeff : DifferentiableAt ℝ c.radialCoefficient x) :
    fderiv ℝ c.accelerationField x =
      c.radialCoefficient x • ContinuousLinearMap.id ℝ Vec3 +
        (fderiv ℝ c.radialCoefficient x).smulRight x := by sorry
