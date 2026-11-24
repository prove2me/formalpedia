-- Prove2me | Theorems.Thm_Matrix_l2_opNorm_le_of_sum_sq_mulVec_le
-- name    : Matrix.l2_opNorm_le_of_sum_sq_mulVec_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:18.771165+00:00
-- url     : https://prove2.me/theorems/89b2ca75-ff57-4f1c-9e34-6795210abb36
-- title:
--   Matrix: l2 op Norm le of sum sq mul Vec le
-- statement:
--   Sum-level form of `Matrix.l2_opNorm_le_of_norm_mulVec_le`: it suffices to bound
--   `∑ i, (A *ᵥ v) i ^ 2` by `C ^ 2 * ∑ j, v j ^ 2` for every plain vector `v`.  Used for the Schur
--   test in Section 11.3 of `bs_lambda.txt`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/SchurTest.lean#L51-L56
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/SchurTest.lean#L51-L56

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
set_option autoImplicit true
@[expose] public section
public section
open scoped Matrix Matrix.Norms.L2Operator
open Matrix
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {C : ℝ}

theorem Matrix.l2_opNorm_le_of_sum_sq_mulVec_le (A : Matrix m n ℝ) (hC : 0 ≤ C)
    (h : ∀ v : n → ℝ, ∑ i, (A *ᵥ v) i ^ 2 ≤ C ^ 2 * ∑ j, v j ^ 2) :
    ‖A‖ ≤ C := by sorry
