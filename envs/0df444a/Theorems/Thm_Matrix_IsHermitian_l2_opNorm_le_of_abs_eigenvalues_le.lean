-- Prove2me | Theorems.Thm_Matrix_IsHermitian_l2_opNorm_le_of_abs_eigenvalues_le
-- name    : Matrix.IsHermitian.l2_opNorm_le_of_abs_eigenvalues_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:59.885348+00:00
-- url     : https://prove2.me/theorems/cbebeb22-942b-4f07-8e5b-1f9fa9996332
-- title:
--   Is Hermitian: l2 op Norm le of abs eigenvalues le
-- statement:
--   The L2 operator norm of a symmetric matrix is bounded by any bound on the absolute values
--   of its eigenvalues.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Hermitian.lean#L44-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Hermitian.lean#L44-L52

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

theorem Matrix.IsHermitian.l2_opNorm_le_of_abs_eigenvalues_le [Nonempty n] (hA : A.IsHermitian) {c : ℝ}
    (hc : ∀ i, |hA.eigenvalues i| ≤ c) : ‖A‖ ≤ c := by sorry
