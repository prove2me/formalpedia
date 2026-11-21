-- Prove2me | Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_inner_eq_dotProduct
-- name    : NewtonianLipschitz.toPhysicalVec3_inner_eq_dotProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:09.228316+00:00
-- url     : https://prove2.me/theorems/2f0beb9a-7dca-4688-88a4-2e2f9d0cb8c9
-- title:
--   Newtonian Lipschitz: to Physical Vec3 inner eq dot Product
-- statement:
--   The physical Euclidean inner product expressed as the Cartesian
--   dot product, without identifying the two vector norms.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L25-L30
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L25-L30

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

theorem NewtonianLipschitz.toPhysicalVec3_inner_eq_dotProduct (x h : Vec3) :
    ⟪toPhysicalVec3 x, toPhysicalVec3 h⟫_ℝ = x ⬝ᵥ h := by sorry
