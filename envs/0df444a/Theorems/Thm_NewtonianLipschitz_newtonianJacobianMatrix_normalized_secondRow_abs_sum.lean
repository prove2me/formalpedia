-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_secondRow_abs_sum
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_normalized_secondRow_abs_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:33:22.418983+00:00
-- url     : https://prove2.me/theorems/4d4275f7-d544-457a-a260-9145a29aa796
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix normalized second Row abs sum
-- statement:
--   Exact absolute sum of the second Jacobian row.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L123-L147
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L123-L147

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_normalized_secondRow_abs_sum
    (μ u v : ℝ) (hμ : 0 ≤ μ)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) :
    (∑ j : Fin 3,
      |newtonianJacobianMatrix μ (normalizedVector u v) 1 j|) =
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        lateralRowNumerator u v := by sorry
