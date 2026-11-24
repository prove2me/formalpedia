-- Prove2me | Theorems.Thm_Matrix_IsHermitian_exists_eigenvector_ciSup_eigenvalues
-- name    : Matrix.IsHermitian.exists_eigenvector_ciSup_eigenvalues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:07.615632+00:00
-- url     : https://prove2.me/theorems/f6d54fe9-861c-4dc2-af17-b070de845334
-- title:
--   Is Hermitian: exists eigenvector ci Sup eigenvalues
-- statement:
--   The largest eigenvalue of a symmetric matrix is attained by an eigenvector.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Hermitian.lean#L75-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Hermitian.lean#L75-L81

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

theorem Matrix.IsHermitian.exists_eigenvector_ciSup_eigenvalues [Nonempty n] (hA : A.IsHermitian) :
    ∃ v : n → ℝ, v ≠ 0 ∧ A *ᵥ v = (⨆ i, hA.eigenvalues i) • v := by sorry
