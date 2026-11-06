-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_total_step_loss
-- name    : OAI.SevenEighths.InverseMoment.total_step_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T23:01:36.145667+00:00
-- url     : https://prove2.me/theorems/b17d8cf4-01d4-40fb-9897-ba9e332f64d0
-- title:
--   Inverse Moment: total step loss
-- statement:
--   The Inverse Moment construction uses the total step loss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Basic.lean#L157-L161
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Basic.lean#L157-L161

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Basic
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment

theorem OAI.SevenEighths.InverseMoment.total_step_loss {D eta tau pi eps : ℝ}
    (h₁ : D * eta ≤ eps / 160) (h₂ : D * tau ≤ eps / 4)
    (h₃ : D * pi ≤ eps / 4) :
    D * (40 * eta + tau + pi) ≤ 3 * eps / 4 := by sorry
