-- Prove2me | Theorems.Thm_Matrix_map_affineLineDet
-- name    : Matrix.map_affineLineDet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:46:36.247174+00:00
-- url     : https://prove2.me/theorems/db9c3160-fa0a-4ada-949e-dd7f214f97ce
-- title:
--   Matrix: map affine Line Det
-- statement:
--   The Matrix construction uses the map affine Line Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L106-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L106-L127

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

theorem Matrix.map_affineLineDet
    {R S n : Type*} [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]
    (f : R →+* S) (A : Matrix n n R) :
    Polynomial.map f (affineLineDet A) = affineLineDet (A.map f) := by sorry
