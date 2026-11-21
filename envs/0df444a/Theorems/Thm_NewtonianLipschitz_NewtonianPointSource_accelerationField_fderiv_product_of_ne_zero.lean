-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_product_of_ne_zero
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_product_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:10.696089+00:00
-- url     : https://prove2.me/theorems/95b29dc2-ada3-4f9d-81f9-79e78bcc775b
-- title:
--   Newtonian Point Source: acceleration Field fderiv product of ne zero
-- statement:
--   Eliminate the formerly supplied radial regularity premise
--   from the product-rule formula, still without evaluating the radial
--   Fréchet derivative explicitly.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Derivative.lean#L93-L99
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Derivative.lean#L93-L99

module
public import Definitions.Def_NewtonianLipschitz_Smoothness
public import Definitions.Def_NewtonianLipschitz_Norms
public import Definitions.Def_NewtonianLipschitz_Derivative
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_product_of_ne_zero
    (c : NewtonianPointSource) (x : Vec3) (hx : x ≠ 0) :
    fderiv ℝ c.accelerationField x =
      c.radialCoefficient x • ContinuousLinearMap.id ℝ Vec3 +
        (fderiv ℝ c.radialCoefficient x).smulRight x := by sorry
