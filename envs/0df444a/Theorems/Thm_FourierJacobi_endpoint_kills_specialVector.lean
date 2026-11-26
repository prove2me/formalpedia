-- Prove2me | Theorems.Thm_FourierJacobi_endpoint_kills_specialVector
-- name    : FourierJacobi.endpoint_kills_specialVector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:41:18.851565+00:00
-- url     : https://prove2.me/theorems/171150ac-1ad9-56e9-9b52-9e692c567668
-- title:
--   Fourier Jacobi: endpoint kills special Vector
-- statement:
--   The Fourier Jacobi construction uses the endpoint kills special Vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Intertwiner.lean#L34-L38
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Intertwiner.lean#L34-L38

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

theorem FourierJacobi.endpoint_kills_specialVector (q : K) (hq : q ≠ 1) :
    (intertwinerMatrix q q⁻¹).mulVec (specialVector q) = 0 := by sorry
