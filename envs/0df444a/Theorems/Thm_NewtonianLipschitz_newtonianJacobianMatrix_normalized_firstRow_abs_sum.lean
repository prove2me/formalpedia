-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_firstRow_abs_sum
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_normalized_firstRow_abs_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:24:11.875041+00:00
-- url     : https://prove2.me/theorems/2a1a905f-ca5e-4a5f-97e4-e6e69a20d6ea
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix normalized first Row abs sum
-- statement:
--   The sum of absolute values in the *actual matrix's* first row
--   is the previously defined dominant numerator divided by the fifth
--   power of the physical Euclidean radius.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L178-L206
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L178-L206

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_JacobianRows
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
set_option autoImplicit true
@[expose] public section
public section
open Matrix WithLp
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_normalized_firstRow_abs_sum
    (μ u v : ℝ) (hμ : 0 ≤ μ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (∑ j : Fin 3,
      |newtonianJacobianMatrix μ (normalizedVector u v) 0 j|) =
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        dominantRowNumerator u v := by sorry
