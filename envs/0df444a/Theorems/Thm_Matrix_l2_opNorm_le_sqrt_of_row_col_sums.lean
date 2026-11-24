-- Prove2me | Theorems.Thm_Matrix_l2_opNorm_le_sqrt_of_row_col_sums
-- name    : Matrix.l2_opNorm_le_sqrt_of_row_col_sums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:30.145769+00:00
-- url     : https://prove2.me/theorems/eda3e9b8-b4a8-463b-9bfa-ecb0e6d947ca
-- title:
--   Matrix: l2 op Norm le sqrt of row col sums
-- statement:
--   **Schur test.**  For a matrix `R` with nonnegative entries whose row sums are bounded by `a`
--   and whose column sums are bounded by `b`, the L2 operator norm satisfies `‖R‖ ≤ sqrt (a * b)`.
--   This is the "standard induced-norm inequality" `‖R‖₂ ≤ sqrt (‖R‖₁ ‖R‖∞)` invoked at the end of
--   Section 11.3 of `bs_lambda.txt`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/SchurTest.lean#L69-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/SchurTest.lean#L69-L84

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
set_option autoImplicit true
@[expose] public section
public section
open scoped Matrix Matrix.Norms.L2Operator
open Matrix
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {C : ℝ}

theorem Matrix.l2_opNorm_le_sqrt_of_row_col_sums (R : Matrix m n ℝ) (hR : ∀ i j, 0 ≤ R i j) {a b : ℝ}
    (hrow : ∀ i, ∑ j, R i j ≤ a) (hcol : ∀ j, ∑ i, R i j ≤ b) :
    ‖R‖ ≤ Real.sqrt (a * b) := by sorry
