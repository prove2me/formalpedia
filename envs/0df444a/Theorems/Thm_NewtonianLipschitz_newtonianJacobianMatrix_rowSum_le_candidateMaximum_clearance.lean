-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_rowSum_le_candidateMaximum_clearance
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_rowSum_le_candidateMaximum_clearance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:54:12.404693+00:00
-- url     : https://prove2.me/theorems/ce459dd0-5264-4591-a38e-1b10633969dc
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix row Sum le candidate Maximum clearance
-- statement:
--   At positive Cartesian clearance d, every absolute row sum
--   is bounded by the sharp scalar candidate times mu / d^3.
--   This is a pointwise result, not a nonconvex global bound.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianCartesianBound.lean#L60-L79
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianCartesianBound.lean#L60-L79

module
public import Definitions.Def_NewtonianLipschitz_JacobianSignedBounds
public import Definitions.Def_NewtonianLipschitz_JacobianCartesianBound
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_rowSum_le_candidateMaximum_clearance
    (μ d : ℝ) (x : Vec3) (i : Fin 3)
    (hμ : 0 ≤ μ) (hd : 0 < d) (hclear : d ≤ ‖x‖) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ x i j|) ≤
      (1 / d ^ 3) * (μ * candidateMaximum) := by sorry
