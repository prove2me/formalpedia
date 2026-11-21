-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_any_safe_axis_tangent_columns_le
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_any_safe_axis_tangent_columns_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T04:01:30.384669+00:00
-- url     : https://prove2.me/theorems/c8675464-367f-4db1-a031-4f9f6e053668
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix any safe axis tangent columns le
-- statement:
--   The physical Newtonian Jacobian has tangent-column row
--   sum at most (5/4)*μ/d³ on ANY of the three safe axes.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialAllAxes.lean#L137-L159
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialAllAxes.lean#L137-L159

module
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialFirstAxis
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialAllAxes
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_any_safe_axis_tangent_columns_le
    (μ d : ℝ) (x : Vec3) (k i : Fin 3)
    (hμ : 0 ≤ μ) (hd : 0 < d) (hx : d ≤ |x i|) :
    (if i = 0 then
      |newtonianJacobianMatrix μ x k 1| +
        |newtonianJacobianMatrix μ x k 2|
     else if i = 1 then
      |newtonianJacobianMatrix μ x k 0| +
        |newtonianJacobianMatrix μ x k 2|
     else
      |newtonianJacobianMatrix μ x k 0| +
        |newtonianJacobianMatrix μ x k 1|) ≤
        (1 / d ^ 3) * (μ * (5 / 4 : ℝ)) := by sorry
