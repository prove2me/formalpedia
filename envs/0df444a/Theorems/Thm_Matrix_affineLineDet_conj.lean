-- Prove2me | Theorems.Thm_Matrix_affineLineDet_conj
-- name    : Matrix.affineLineDet_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:46:49.810479+00:00
-- url     : https://prove2.me/theorems/7eb5222b-eac8-42b3-95da-bf042ff27066
-- title:
--   Matrix: affine Line Det conj
-- statement:
--   The normalized affine-line determinant is invariant under conjugation by
--   a matrix with a supplied right inverse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L131-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L131-L169

import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Tactic.NoncommRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
set_option autoImplicit false
open scoped Matrix
open Matrix
open scoped Polynomial

theorem Matrix.affineLineDet_conj
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A Z Zi : Matrix n n R) (hZZi : Z * Zi = 1) :
    affineLineDet (Z * A * Zi) = affineLineDet A := by sorry
