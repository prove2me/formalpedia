-- Prove2me | Theorems.Thm_FourierJacobi_LocalMatrix_all_two_by_two_minors
-- name    : FourierJacobi.LocalMatrix.all_two_by_two_minors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:08.485381+00:00
-- url     : https://prove2.me/theorems/0e3d4c67-8d87-41ed-9cd3-e088383f4db2
-- title:
--   Local Matrix: all two by two minors
-- statement:
--   The Local Matrix construction uses the all two by two minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L109-L120
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L109-L120

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

theorem FourierJacobi.LocalMatrix.all_two_by_two_minors (a x y z : K) (ha : a ≠ 0) :
    secondCompound (g a x y z) =
      !![a, a * x, a * y, -a * y, -a * z, a * (y ^ 2 - x * z);
         0, a⁻¹, 0, 0, 0, -z / a;
         0, 0, 1, 0, 0, y;
         0, 0, 0, 1, 0, -y;
         0, 0, 0, 0, a, a * x;
         0, 0, 0, 0, 0, a⁻¹] := by sorry
