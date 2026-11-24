-- Prove2me | Theorems.Thm_Matrix_l2_opNorm_transpose
-- name    : Matrix.l2_opNorm_transpose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:49:16.219675+00:00
-- url     : https://prove2.me/theorems/37f42478-a5b2-4a81-b569-268e87995681
-- title:
--   Matrix: l2 op Norm transpose
-- statement:
--   Over `ℝ` the transpose coincides with the conjugate transpose, so it preserves the L2
--   operator norm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/SchurTest.lean#L36-L37
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/SchurTest.lean#L36-L37

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
set_option autoImplicit true
@[expose] public section
public section
open scoped Matrix Matrix.Norms.L2Operator
open Matrix
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {C : ℝ}

theorem Matrix.l2_opNorm_transpose [DecidableEq m] (A : Matrix m n ℝ) : ‖Aᵀ‖ = ‖A‖ := by sorry
