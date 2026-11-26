-- Prove2me | Theorems.Thm_FourierJacobi_compactGram_special_norm_sq
-- name    : FourierJacobi.compactGram_special_norm_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:41:20.970752+00:00
-- url     : https://prove2.me/theorems/da4c0d43-25bd-55c8-8db4-14e077a4cfff
-- title:
--   Fourier Jacobi: compact Gram special norm sq
-- statement:
--   The Fourier Jacobi construction uses the compact Gram special norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Intertwiner.lean#L50-L55
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/Intertwiner.lean#L50-L55

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

theorem FourierJacobi.compactGram_special_norm_sq (q : ℝ) (hq : 1 < q) :
    dotProduct (specialVector q) ((compactGram q).mulVec (specialVector q)) = q⁻¹ := by sorry
