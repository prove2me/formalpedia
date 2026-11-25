-- Prove2me | Theorems.Thm_Matrix_det_eq_corner_mul_det_submatrix
-- name    : Matrix.det_eq_corner_mul_det_submatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:20:06.117886+00:00
-- url     : https://prove2.me/theorems/3e2a6944-8eb2-4dca-acc4-d1205b42f773
-- title:
--   Matrix: det eq corner mul det submatrix
-- statement:
--   **Bordered determinant.** Let `M` be a `(k+1)×(k+1)` matrix and `w` a
--   vector of `k` scalars such that the entries of the last column of `M` above the
--   corner are given by the combination of the first `k` columns with coefficients
--   `w`, i.e. `M i last = ∑ⱼ M i j · wⱼ` for `i < k`. Then
--
--     `det M = (M last last - ∑ⱼ M last j · wⱼ) · det (M restricted to the first k
--     rows and columns)`.
--
--   No invertibility of the top-left block is required; this is the elementary
--   column-operation form of the Schur determinant formula.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Determinant.lean#L78-L128
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Determinant.lean#L78-L128

module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Determinant
public import Definitions.Def_BasicResults_Determinant
set_option autoImplicit true
@[expose] public section
public section
open LinearMap
open scoped ComplexConjugate
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

theorem Matrix.det_eq_corner_mul_det_submatrix {R : Type*} [CommRing R] {k : ℕ}
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (w : Fin k → R)
    (hw : ∀ i : Fin k, M i.castSucc (Fin.last k)
      = ∑ j, M i.castSucc j.castSucc * w j) :
    M.det = (M (Fin.last k) (Fin.last k) - ∑ j, M (Fin.last k) j.castSucc * w j)
      * (M.submatrix Fin.castSucc Fin.castSucc).det := by sorry
