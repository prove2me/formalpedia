-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_markedMargins_of_strict
-- name    : OAI.SevenEighths.InverseMoment.markedMargins_of_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T23:01:02.238996+00:00
-- url     : https://prove2.me/theorems/0aee3a55-48b5-4caf-9d79-835e80cfa461
-- title:
--   Inverse Moment: marked Margins of strict
-- statement:
--   The Inverse Moment construction uses the marked Margins of strict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Basic.lean#L16-L25
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Basic.lean#L16-L25

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Basic
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment

theorem OAI.SevenEighths.InverseMoment.markedMargins_of_strict {m r z : ℝ}
    (h₁ : r + 2 * z < m) (h₂ : 2 * r + 8 * z < 3 * m) :
    ∃ c > 0, MarkedMargins m r z c := by sorry
