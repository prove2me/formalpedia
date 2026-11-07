-- Prove2me | Theorems.Thm_Matrix_algebraNorm_eq_det_pow_card
-- name    : Matrix.algebraNorm_eq_det_pow_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:47:06.982796+00:00
-- url     : https://prove2.me/theorems/fd786a5c-decc-4289-93e3-7e6e369ef8b4
-- title:
--   Matrix: algebra Norm eq det pow card
-- statement:
--   The regular algebra norm on `M_n(R)` is `det^n`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L190-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L190-L199

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

theorem Matrix.algebraNorm_eq_det_pow_card
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) :
    Algebra.norm R A = Matrix.det A ^ Fintype.card n := by sorry
