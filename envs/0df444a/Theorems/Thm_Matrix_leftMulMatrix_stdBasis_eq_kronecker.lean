-- Prove2me | Theorems.Thm_Matrix_leftMulMatrix_stdBasis_eq_kronecker
-- name    : Matrix.leftMulMatrix_stdBasis_eq_kronecker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:55:00.220342+00:00
-- url     : https://prove2.me/theorems/6cb2b0e7-96f6-4271-b263-ef05a9c41d0e
-- title:
--   Matrix: left Mul Matrix std Basis eq kronecker
-- statement:
--   In the standard matrix-unit basis, left multiplication by `A` is the
--   Kronecker product of `A` with the identity matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L173-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L173-L187

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

theorem Matrix.leftMulMatrix_stdBasis_eq_kronecker
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) :
    Algebra.leftMulMatrix (Matrix.stdBasis R n n) A =
      Matrix.kronecker A (1 : Matrix n n R) := by sorry
