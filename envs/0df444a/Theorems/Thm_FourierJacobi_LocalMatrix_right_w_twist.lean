-- Prove2me | Theorems.Thm_FourierJacobi_LocalMatrix_right_w_twist
-- name    : FourierJacobi.LocalMatrix.right_w_twist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:28.541697+00:00
-- url     : https://prove2.me/theorems/9aab2d62-e505-425f-88ea-ab3a18d62e69
-- title:
--   Local Matrix: right w twist
-- statement:
--   The Local Matrix construction uses the right w twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L79-L82
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L79-L82

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

theorem FourierJacobi.LocalMatrix.right_w_twist (a x y z p : K) (ha : a ≠ 0) (hp : p ≠ 0) :
    E p⁻¹ * g a x y z * w * E p =
      D (a * p) * N (x / p) (y / p) (z / p) * w := by sorry
