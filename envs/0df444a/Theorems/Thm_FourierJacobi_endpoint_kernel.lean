-- Prove2me | Theorems.Thm_FourierJacobi_endpoint_kernel
-- name    : FourierJacobi.endpoint_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:41:22.071986+00:00
-- url     : https://prove2.me/theorems/ef32038e-606c-4aa5-a71e-b04ce5fc164f
-- title:
--   Fourier Jacobi: endpoint kernel
-- statement:
--   The Fourier Jacobi construction uses the endpoint kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Intertwiner.lean#L40-L44
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Intertwiner.lean#L40-L44

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

theorem FourierJacobi.endpoint_kernel (q : K) (hq : q ≠ 1) (v : Fin 2 → K) :
    (intertwinerMatrix q q⁻¹).mulVec v = 0 ↔ v 1 = -q⁻¹ * v 0 := by sorry
