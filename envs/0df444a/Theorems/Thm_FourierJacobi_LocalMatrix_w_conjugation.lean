-- Prove2me | Theorems.Thm_FourierJacobi_LocalMatrix_w_conjugation
-- name    : FourierJacobi.LocalMatrix.w_conjugation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:35.164095+00:00
-- url     : https://prove2.me/theorems/1893bbe4-3fcb-50b8-a047-c139996747da
-- title:
--   Local Matrix: w conjugation
-- statement:
--   The Local Matrix construction uses the w conjugation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L89-L92
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L89-L92

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

theorem FourierJacobi.LocalMatrix.w_conjugation (a x y z : K) :
    wInv * g a x y z * w =
      !![1, -y, 0, z; 0, a⁻¹, 0, 0; 0, -a * x, a, a * y; 0, 0, 0, 1] := by sorry
