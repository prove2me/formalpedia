-- Prove2me | Theorems.Thm_Matrix_det_eq_of_algEquiv
-- name    : Matrix.det_eq_of_algEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:47:08.975211+00:00
-- url     : https://prove2.me/theorems/4a415b08-6cea-48c6-816b-1c4e6b61d0a6
-- title:
--   Matrix: det eq of alg Equiv
-- statement:
--   Over a field, the determinant attached to a splitting of an algebra is
--   independent of the chosen algebra equivalence with a matrix algebra.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L203-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L203-L208

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

theorem Matrix.det_eq_of_algEquiv
    {K A n : Type*} [Field K] [Ring A] [Algebra K A]
    [Fintype n] [DecidableEq n]
    (e₁ e₂ : A ≃ₐ[K] Matrix n n K) (x : A) :
    Matrix.det (e₁ x) = Matrix.det (e₂ x) := by sorry
