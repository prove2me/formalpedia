-- Prove2me | Theorems.Thm_Matrix_IsHermitian_le_ciSup_eigenvalues
-- name    : Matrix.IsHermitian.le_ciSup_eigenvalues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:01.72371+00:00
-- url     : https://prove2.me/theorems/d1cd777f-3f84-4eac-8b82-0a1079562e4a
-- title:
--   Is Hermitian: le ci Sup eigenvalues
-- statement:
--   Every eigenvalue of a symmetric matrix is at most the largest eigenvalue.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Hermitian.lean#L55-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Hermitian.lean#L55-L63

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

theorem Matrix.IsHermitian.le_ciSup_eigenvalues (hA : A.IsHermitian) {μ : ℝ} {v : n → ℝ} (hv : v ≠ 0)
    (hev : A *ᵥ v = μ • v) : μ ≤ ⨆ i, hA.eigenvalues i := by sorry
