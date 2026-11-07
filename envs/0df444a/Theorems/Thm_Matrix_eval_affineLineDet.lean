-- Prove2me | Theorems.Thm_Matrix_eval_affineLineDet
-- name    : Matrix.eval_affineLineDet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:54:32.856199+00:00
-- url     : https://prove2.me/theorems/e11f8b68-431e-4376-bb07-101dcba76124
-- title:
--   Matrix: eval affine Line Det
-- statement:
--   The Matrix construction uses the eval affine Line Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L71-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L71-L89

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

theorem Matrix.eval_affineLineDet
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (a : R) :
    Polynomial.eval a (affineLineDet A) =
      Matrix.det ((1 : Matrix n n R) + a • (A - 1)) := by sorry
