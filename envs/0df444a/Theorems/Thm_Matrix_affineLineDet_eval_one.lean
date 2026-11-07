-- Prove2me | Theorems.Thm_Matrix_affineLineDet_eval_one
-- name    : Matrix.affineLineDet_eval_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:46:24.905015+00:00
-- url     : https://prove2.me/theorems/56aed329-325a-4de1-ab69-27b501ac8536
-- title:
--   Matrix: affine Line Det eval one
-- statement:
--   The Matrix construction uses the affine Line Det eval one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L98-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L98-L104

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

theorem Matrix.affineLineDet_eval_one
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) :
    Polynomial.eval 1 (affineLineDet A) = Matrix.det A := by sorry
