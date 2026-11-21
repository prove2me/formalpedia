-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_eq_jacobianMatrix
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_eq_jacobianMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:23:38.78074+00:00
-- url     : https://prove2.me/theorems/69cf5836-7c63-47f7-9d4c-a9067d717337
-- title:
--   Newtonian Point Source: acceleration Field fderiv eq jacobian Matrix
-- statement:
--   The actual Fréchet derivative of the physical Newtonian field
--   agrees, in every direction, with the explicit Cartesian matrix.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L93-L99
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L93-L99

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_JacobianRows
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
set_option autoImplicit true
@[expose] public section
public section
open Matrix WithLp
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_eq_jacobianMatrix
    (c : NewtonianPointSource) (x h : Vec3) (hx : x ≠ 0) :
    (fderiv ℝ c.accelerationField x) h =
      newtonianJacobianMatrix c.gravitationalParameter x *ᵥ h := by sorry
