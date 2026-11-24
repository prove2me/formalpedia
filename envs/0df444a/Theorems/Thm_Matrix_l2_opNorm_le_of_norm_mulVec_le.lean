-- Prove2me | Theorems.Thm_Matrix_l2_opNorm_le_of_norm_mulVec_le
-- name    : Matrix.l2_opNorm_le_of_norm_mulVec_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:08.494302+00:00
-- url     : https://prove2.me/theorems/0271f61e-668a-4894-8c09-d87cdec30d26
-- title:
--   Matrix: l2 op Norm le of norm mul Vec le
-- statement:
--   Converse of `Matrix.l2_opNorm_mulVec`: if every Euclidean vector `v` satisfies
--   `‖A *ᵥ v‖ ≤ C * ‖v‖`, then the L2 operator norm of `A` is at most `C`.  This is the entry point
--   for the Schur test of Section 11.3 of `bs_lambda.txt`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/SchurTest.lean#L42-L46
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/SchurTest.lean#L42-L46

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
set_option autoImplicit true
@[expose] public section
public section
open scoped Matrix Matrix.Norms.L2Operator
open Matrix
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {C : ℝ}

theorem Matrix.l2_opNorm_le_of_norm_mulVec_le (A : Matrix m n ℝ) (hC : 0 ≤ C)
    (h : ∀ v : EuclideanSpace ℝ n, ‖(EuclideanSpace.equiv m ℝ).symm (A *ᵥ v)‖ ≤ C * ‖v‖) :
    ‖A‖ ≤ C := by sorry
