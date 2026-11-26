-- Prove2me | Theorems.Thm_FourierJacobi_LocalMatrix_w_mul_wInv
-- name    : FourierJacobi.LocalMatrix.w_mul_wInv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:12.515841+00:00
-- url     : https://prove2.me/theorems/78c3540e-9e1e-5dbe-bfe4-bd6ed4e2fcd1
-- title:
--   Local Matrix: w mul w Inv
-- statement:
--   The Local Matrix construction uses the w mul w Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L51-L52
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L51-L52

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

theorem FourierJacobi.LocalMatrix.w_mul_wInv : (w : Matrix (Fin 4) (Fin 4) K) * wInv = 1 := by sorry
