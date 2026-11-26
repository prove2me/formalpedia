-- Prove2me | Theorems.Thm_FourierJacobi_LocalMatrix_twist_conjugation
-- name    : FourierJacobi.LocalMatrix.twist_conjugation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:21.580035+00:00
-- url     : https://prove2.me/theorems/5ed10a68-10dd-4bac-b785-3c834b4c7167
-- title:
--   Local Matrix: twist conjugation
-- statement:
--   The Local Matrix construction uses the twist conjugation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L71-L73
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Matrices.lean#L71-L73

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

theorem FourierJacobi.LocalMatrix.twist_conjugation (a x y z p : K) (hp : p ≠ 0) :
    E p⁻¹ * g a x y z * E p = D a * N (p * x) y (z / p) := by sorry
