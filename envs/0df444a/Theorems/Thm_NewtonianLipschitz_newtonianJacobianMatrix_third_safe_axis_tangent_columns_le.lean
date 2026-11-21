-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_third_safe_axis_tangent_columns_le
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_third_safe_axis_tangent_columns_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:52:29.89703+00:00
-- url     : https://prove2.me/theorems/73011440-8d8d-4a9b-b4c0-d6bf9f568512
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix third safe axis tangent columns le
-- statement:
--   When the third coordinate is fixed and safe, the
--   remaining physical Jacobian columns 0 and 1 obey 5/4.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialAllAxes.lean#L44-L57
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialAllAxes.lean#L44-L57

module
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialFirstAxis
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialAllAxes
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_third_safe_axis_tangent_columns_le
    (μ d : ℝ) (x : Vec3) (k : Fin 3)
    (hμ : 0 ≤ μ) (hd : 0 < d) (hx : d ≤ |x 2|) :
    |newtonianJacobianMatrix μ x k 0| +
        |newtonianJacobianMatrix μ x k 1| ≤
      (1 / d ^ 3) * (μ * (5 / 4 : ℝ)) := by sorry
