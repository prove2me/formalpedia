-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_marked_inactive_coefficient
-- name    : OAI.SevenEighths.InverseMoment.marked_inactive_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T23:00:14.374637+00:00
-- url     : https://prove2.me/theorems/2422370a-4dfb-4307-8828-e8f1079cacd9
-- title:
--   Inverse Moment: marked inactive coefficient
-- statement:
--   The Inverse Moment construction uses the marked inactive coefficient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/LocalReflection.lean#L56-L59
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/LocalReflection.lean#L56-L59

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

theorem OAI.SevenEighths.InverseMoment.marked_inactive_coefficient (ψ : AddChar F ℂ) :
    (Fintype.card F : ℂ)⁻¹ * localFourier zeroMark ψ 0 =
      (Fintype.card F : ℂ)⁻¹ := by sorry
