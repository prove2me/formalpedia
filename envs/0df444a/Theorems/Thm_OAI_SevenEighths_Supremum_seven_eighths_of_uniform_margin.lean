-- Prove2me | Theorems.Thm_OAI_SevenEighths_Supremum_seven_eighths_of_uniform_margin
-- name    : OAI.SevenEighths.Supremum.seven_eighths_of_uniform_margin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:44:34.020416+00:00
-- url     : https://prove2.me/theorems/1039583c-3cb8-4375-ba88-b629aa848391
-- title:
--   Supremum: seven eighths of uniform margin
-- statement:
--   The Supremum construction uses the seven eighths of uniform margin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Supremum.lean#L68-L77
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Supremum.lean#L68-L77

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section

theorem OAI.SevenEighths.Supremum.seven_eighths_of_uniform_margin {S : Set ℝ}
    (hne : S.Nonempty) (hbounded : BddAbove S)
    (hbound : 7 / 8 < sSup S →
      ∃ ω σ : ℝ, ω < sSup S - 7 / 8 ∧ 0 < σ ∧
        ∀ x ∈ S, x ≤ sSup S - continuationMargin (sSup S) ω σ) :
    sSup S ≤ 7 / 8 := by sorry
