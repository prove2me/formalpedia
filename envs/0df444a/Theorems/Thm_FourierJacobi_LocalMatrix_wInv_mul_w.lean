-- Prove2me | Theorems.Thm_FourierJacobi_LocalMatrix_wInv_mul_w
-- name    : FourierJacobi.LocalMatrix.wInv_mul_w
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:14.435834+00:00
-- url     : https://prove2.me/theorems/4423fa96-cc4c-5dd8-a150-8234677e7a62
-- title:
--   Local Matrix: w Inv mul w
-- statement:
--   The Local Matrix construction uses the w Inv mul w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L54-L55
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L54-L55

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

theorem FourierJacobi.LocalMatrix.wInv_mul_w : (wInv : Matrix (Fin 4) (Fin 4) K) * w = 1 := by sorry
