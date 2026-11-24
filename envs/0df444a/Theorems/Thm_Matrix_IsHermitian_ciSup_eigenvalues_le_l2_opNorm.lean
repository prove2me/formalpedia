-- Prove2me | Theorems.Thm_Matrix_IsHermitian_ciSup_eigenvalues_le_l2_opNorm
-- name    : Matrix.IsHermitian.ciSup_eigenvalues_le_l2_opNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:06.971704+00:00
-- url     : https://prove2.me/theorems/d5fc65f0-fee1-4b52-b834-46c3377aa59b
-- title:
--   Is Hermitian: ci Sup eigenvalues le l2 op Norm
-- statement:
--   The largest eigenvalue of a symmetric matrix is at most its L2 operator norm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Hermitian.lean#L66-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Hermitian.lean#L66-L72

module
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Hermitian
set_option autoImplicit true
@[expose] public section
public section
open Matrix Matrix.IsHermitian
open scoped Matrix Matrix.Norms.L2Operator
variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

theorem Matrix.IsHermitian.ciSup_eigenvalues_le_l2_opNorm [Nonempty n] (hA : A.IsHermitian) :
    ⨆ i, hA.eigenvalues i ≤ ‖A‖ := by sorry
