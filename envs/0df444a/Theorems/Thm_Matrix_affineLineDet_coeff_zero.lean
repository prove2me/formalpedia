-- Prove2me | Theorems.Thm_Matrix_affineLineDet_coeff_zero
-- name    : Matrix.affineLineDet_coeff_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:32:10.387106+00:00
-- url     : https://prove2.me/theorems/2c1f9ebd-d4f5-4356-aa4f-246ec03aa221
-- title:
--   Matrix: affine Line Det coeff zero
-- statement:
--   The Matrix construction uses the affine Line Det coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L91-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L91-L96

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

theorem Matrix.affineLineDet_coeff_zero
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) :
    (affineLineDet A).coeff 0 = 1 := by sorry
