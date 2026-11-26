-- Prove2me | Theorems.Thm_FourierJacobi_intertwinerMatrix_at_endpoint
-- name    : FourierJacobi.intertwinerMatrix_at_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:40:42.28096+00:00
-- url     : https://prove2.me/theorems/a2f1e3a4-2d78-4f7a-8e8e-9fb1c2ce5be3
-- title:
--   Fourier Jacobi: intertwiner Matrix at endpoint
-- statement:
--   The Fourier Jacobi construction uses the intertwiner Matrix at endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Intertwiner.lean#L26-L30
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Intertwiner.lean#L26-L30

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Definitions.Def_FourierJacobi_Algebra_Intertwiner
set_option autoImplicit false
open FourierJacobi
open Matrix
variable {K : Type*} [Field K]

theorem FourierJacobi.intertwinerMatrix_at_endpoint (q : K) (hq : q ≠ 1) :
    intertwinerMatrix q q⁻¹ = !![q⁻¹, 1; q⁻¹, 1] := by sorry
