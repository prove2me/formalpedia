-- Prove2me | Theorems.Thm_FourierJacobi_LocalMatrix_w_remove_two_coordinates
-- name    : FourierJacobi.LocalMatrix.w_remove_two_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:36.97144+00:00
-- url     : https://prove2.me/theorems/9c51ddc8-cbd5-54fe-af63-b25f57512188
-- title:
--   Local Matrix: w remove two coordinates
-- statement:
--   The Local Matrix construction uses the w remove two coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L94-L97
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L94-L97

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

theorem FourierJacobi.LocalMatrix.w_remove_two_coordinates (a x y z r s : K) (ha : a ≠ 0) :
    YZ r 0 * wInv * N (-s) 0 0 * X (-r) * D a * N x y z * w =
      wInv * D a * N (x - s / a ^ 2) (y - r * s / a) (z - r ^ 2 * s) * w := by sorry
