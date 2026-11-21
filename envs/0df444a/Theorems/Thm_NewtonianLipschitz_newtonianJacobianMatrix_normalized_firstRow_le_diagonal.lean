-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_firstRow_le_diagonal
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_normalized_firstRow_le_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:38.485676+00:00
-- url     : https://prove2.me/theorems/ddda6d68-a548-474e-8083-2744f4485d7a
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix normalized first Row le diagonal
-- statement:
--   On the normalized nonnegative octant, the *actual* first-row
--   absolute sum is bounded by the diagonal numerator at equal Euclidean
--   radius. This is a step toward, not the complete global sharp bound.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L211-L227
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean#L211-L227

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

theorem NewtonianLipschitz.newtonianJacobianMatrix_normalized_firstRow_le_diagonal
    (μ u v : ℝ) (hμ : 0 ≤ μ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (∑ j : Fin 3,
      |newtonianJacobianMatrix μ (normalizedVector u v) 0 j|) ≤
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        dominantRowNumerator (diagonalParameter u v)
          (diagonalParameter u v) := by sorry
