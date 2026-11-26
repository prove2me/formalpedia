-- Prove2me | Theorems.Thm_FourierJacobi_LocalMatrix_minus_twist
-- name    : FourierJacobi.LocalMatrix.minus_twist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:24.189846+00:00
-- url     : https://prove2.me/theorems/35d0335b-6d4d-51be-a756-3dcfa439b929
-- title:
--   Local Matrix: minus twist
-- statement:
--   The Local Matrix construction uses the minus twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L75-L77
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L75-L77

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

theorem FourierJacobi.LocalMatrix.minus_twist (a x y z : K) :
    E (-1) * g a x y z * E (-1) = D a * N (-x) y (-z) := by sorry
