-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_critical_firstRow_eq_candidateMaximum
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_critical_firstRow_eq_candidateMaximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:34:54.817606+00:00
-- url     : https://prove2.me/theorems/fe22f651-51c4-4ce1-927c-aabe9519337e
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix critical first Row eq candidate Maximum
-- statement:
--   The sharp candidate row bound is attained by an actual
--   Newtonian Jacobian at a Cartesian unit displacement.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSharpWitness.lean#L67-L78
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSharpWitness.lean#L67-L78

module
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorNorm
public import Definitions.Def_NewtonianLipschitz_JacobianSharpWitness
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_critical_firstRow_eq_candidateMaximum :
    (∑ j : Fin 3,
      |newtonianJacobianMatrix (1 : ℝ)
        (normalizedVector candidateCriticalPoint candidateCriticalPoint)
          0 j|) = candidateMaximum := by sorry
