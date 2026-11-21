-- Prove2me | Theorems.Thm_NewtonianLipschitz_normalizedVector_radius_sq
-- name    : NewtonianLipschitz.normalizedVector_radius_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:23:32.777066+00:00
-- url     : https://prove2.me/theorems/ffa8b819-83f4-4cd6-9d1a-101212c0567d
-- title:
--   Newtonian Lipschitz: normalized Vector radius sq
-- statement:
--   Square of the physical Euclidean radius of the normalized vector.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L138-L145
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L138-L145

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

theorem NewtonianLipschitz.normalizedVector_radius_sq (u v : ℝ) :
    euclideanRadius (normalizedVector u v) ^ 2 =
      1 + u ^ 2 + v ^ 2 := by sorry
