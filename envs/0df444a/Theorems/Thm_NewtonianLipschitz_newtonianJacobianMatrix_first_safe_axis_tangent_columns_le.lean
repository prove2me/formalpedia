-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_first_safe_axis_tangent_columns_le
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_first_safe_axis_tangent_columns_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:52:13.391539+00:00
-- url     : https://prove2.me/theorems/e7ac981d-8ab3-4ea6-94fc-925a63b61584
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix first safe axis tangent columns le
-- statement:
--   For arbitrary signed x whose first Cartesian coordinate
--   is at least d in magnitude, the ACTUAL Newtonian Jacobian's
--   two tangent columns have restricted absolute row sum at
--   most (5/4)*μ/d³.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialFirstAxis.lean#L29-L98
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialFirstAxis.lean#L29-L98

module
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialNormalized
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialFirstAxis
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_first_safe_axis_tangent_columns_le
    (μ d : ℝ) (x : Vec3) (k : Fin 3)
    (hμ : 0 ≤ μ) (hd : 0 < d) (hx : d ≤ |x 0|) :
    |newtonianJacobianMatrix μ x k 1| +
        |newtonianJacobianMatrix μ x k 2| ≤
      (1 / d ^ 3) * (μ * (5 / 4 : ℝ)) := by sorry
