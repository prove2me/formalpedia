-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_second_safe_axis_tangent_columns_le
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_second_safe_axis_tangent_columns_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:52:34.689605+00:00
-- url     : https://prove2.me/theorems/630790d5-1752-4595-83d2-fca0259e5094
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix second safe axis tangent columns le
-- statement:
--   When the second coordinate is the fixed safe coordinate, the
--   remaining columns 0 and 2 of every row obey the same physical
--   Newtonian 5/4 estimate.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialAllAxes.lean#L27-L40
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialAllAxes.lean#L27-L40

module
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialFirstAxis
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialAllAxes
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_second_safe_axis_tangent_columns_le
    (μ d : ℝ) (x : Vec3) (k : Fin 3)
    (hμ : 0 ≤ μ) (hd : 0 < d) (hx : d ≤ |x 1|) :
    |newtonianJacobianMatrix μ x k 0| +
        |newtonianJacobianMatrix μ x k 2| ≤
      (1 / d ^ 3) * (μ * (5 / 4 : ℝ)) := by sorry
