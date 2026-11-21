-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_secondRow_le_candidateMaximum
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_normalized_secondRow_le_candidateMaximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:33:19.714372+00:00
-- url     : https://prove2.me/theorems/99cfa9b7-8eec-42d2-9051-b39626783bdb
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix normalized second Row le candidate Maximum
-- statement:
--   The second physical row satisfies the exact scalar candidate
--   bound in the nonnegative normalized octant.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L151-L180
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L151-L180

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_normalized_secondRow_le_candidateMaximum
    (μ u v : ℝ) (hμ : 0 ≤ μ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (∑ j : Fin 3,
      |newtonianJacobianMatrix μ (normalizedVector u v) 1 j|) ≤
      μ * candidateMaximum := by sorry
