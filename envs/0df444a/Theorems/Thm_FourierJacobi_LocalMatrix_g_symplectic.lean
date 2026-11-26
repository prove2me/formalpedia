-- Prove2me | Theorems.Thm_FourierJacobi_LocalMatrix_g_symplectic
-- name    : FourierJacobi.LocalMatrix.g_symplectic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:14.990951+00:00
-- url     : https://prove2.me/theorems/e8cf5268-9117-55ea-b74c-933b336dbe19
-- title:
--   Local Matrix: g symplectic
-- statement:
--   The Local Matrix construction uses the g symplectic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L57-L59
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L57-L59

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

theorem FourierJacobi.LocalMatrix.g_symplectic (a x y z : K) (ha : a ≠ 0) :
    (g a x y z).transpose * J * g a x y z = J := by sorry
