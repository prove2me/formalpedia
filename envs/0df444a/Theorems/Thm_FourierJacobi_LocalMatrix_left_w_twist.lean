-- Prove2me | Theorems.Thm_FourierJacobi_LocalMatrix_left_w_twist
-- name    : FourierJacobi.LocalMatrix.left_w_twist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:35.953899+00:00
-- url     : https://prove2.me/theorems/d6d7e3f5-3798-4cea-9760-e3793949c9fd
-- title:
--   Local Matrix: left w twist
-- statement:
--   The Local Matrix construction uses the left w twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L84-L87
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L84-L87

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_FourierJacobi_Algebra_Matrices
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.LocalMatrix
open Matrix
variable {K : Type*} [Field K]

theorem FourierJacobi.LocalMatrix.left_w_twist (a x y z p : K) (ha : a ≠ 0) (hp : p ≠ 0) :
    E p⁻¹ * wInv * g a x y z * E p =
      wInv * D (a / p) * N (p * x) y (z / p) := by sorry
