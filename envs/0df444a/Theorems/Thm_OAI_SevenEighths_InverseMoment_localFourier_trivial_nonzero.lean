-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_localFourier_trivial_nonzero
-- name    : OAI.SevenEighths.InverseMoment.localFourier_trivial_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:24:10.922232+00:00
-- url     : https://prove2.me/theorems/cd1044e4-48ee-4129-82c5-f453bdfd898b
-- title:
--   Inverse Moment: local Fourier trivial nonzero
-- statement:
--   The Inverse Moment construction uses the local Fourier trivial nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/LocalReflection.lean#L24-L28
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/LocalReflection.lean#L24-L28

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_LocalReflection
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] [Fintype F]

theorem OAI.SevenEighths.InverseMoment.localFourier_trivial_nonzero (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (h : F) (hh : h ≠ 0) :
    localFourier (fun t => (1 : MulChar F ℂ) t) ψ h = -1 := by sorry
