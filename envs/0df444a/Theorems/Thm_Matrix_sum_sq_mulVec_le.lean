-- Prove2me | Theorems.Thm_Matrix_sum_sq_mulVec_le
-- name    : Matrix.sum_sq_mulVec_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:22.107474+00:00
-- url     : https://prove2.me/theorems/0f7f4118-8e45-4381-9371-edfbb1407b17
-- title:
--   Matrix: sum sq mul Vec le
-- statement:
--   Sum form of `Matrix.l2_opNorm_mulVec`: the defining operator bound, with both norms
--   squared and written out as sums.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/SchurTest.lean#L60-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/SchurTest.lean#L60-L63

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
set_option autoImplicit true
@[expose] public section
public section
open scoped Matrix Matrix.Norms.L2Operator
open Matrix
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {C : ℝ}

theorem Matrix.sum_sq_mulVec_le (A : Matrix m n ℝ) (v : n → ℝ) :
    ∑ i, (A *ᵥ v) i ^ 2 ≤ ‖A‖ ^ 2 * ∑ j, v j ^ 2 := by sorry
