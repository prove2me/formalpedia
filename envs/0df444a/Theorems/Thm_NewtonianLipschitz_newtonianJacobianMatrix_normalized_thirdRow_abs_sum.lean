-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_thirdRow_abs_sum
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_normalized_thirdRow_abs_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:33:52.28746+00:00
-- url     : https://prove2.me/theorems/d65460d2-3f7e-4205-88c9-5791bc3f8177
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix normalized third Row abs sum
-- statement:
--   The third absolute-row sum is the swapped lateral numerator.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L216-L240
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L216-L240

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_normalized_thirdRow_abs_sum
    (μ u v : ℝ) (hμ : 0 ≤ μ)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) :
    (∑ j : Fin 3,
      |newtonianJacobianMatrix μ (normalizedVector u v) 2 j|) =
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        lateralRowNumerator v u := by sorry
