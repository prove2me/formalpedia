-- Prove2me | Theorems.Thm_FourierJacobi_LocalMatrix_remove_two_coordinates
-- name    : FourierJacobi.LocalMatrix.remove_two_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:19.792452+00:00
-- url     : https://prove2.me/theorems/246819c4-1bb1-4a1b-9f0c-4d43303b69cf
-- title:
--   Local Matrix: remove two coordinates
-- statement:
--   The Local Matrix construction uses the remove two coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L66-L69
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L66-L69

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

theorem FourierJacobi.LocalMatrix.remove_two_coordinates (a x y z t r : K) (ha : a ≠ 0) :
    N t 0 0 * X (-r) * g a x y z =
      X (-r) * D a * N (x + t / a ^ 2) (y + r * t / a) (z + r ^ 2 * t) := by sorry
