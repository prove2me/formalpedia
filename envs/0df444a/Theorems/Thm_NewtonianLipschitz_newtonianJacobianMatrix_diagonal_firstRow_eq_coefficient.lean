-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_diagonal_firstRow_eq_coefficient
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_diagonal_firstRow_eq_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:36:01.901778+00:00
-- url     : https://prove2.me/theorems/4c6a6964-e6da-4b1a-99ac-010587a70e13
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix diagonal first Row eq coefficient
-- statement:
--   Exact first absolute Jacobian row sum on the nonnegative
--   diagonal, expressed using the scalar candidate function.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSharpWitness.lean#L36-L51
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSharpWitness.lean#L36-L51

module
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorNorm
public import Definitions.Def_NewtonianLipschitz_JacobianSharpWitness
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_diagonal_firstRow_eq_coefficient
    (μ t : ℝ) (hμ : 0 ≤ μ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑ j : Fin 3,
      |newtonianJacobianMatrix μ (normalizedVector t t) 0 j|) =
        μ * candidateCoefficient t := by sorry
