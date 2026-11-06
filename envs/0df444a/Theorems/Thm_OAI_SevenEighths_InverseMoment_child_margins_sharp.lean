-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_child_margins_sharp
-- name    : OAI.SevenEighths.InverseMoment.child_margins_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:27:36.746767+00:00
-- url     : https://prove2.me/theorems/800710ec-2b39-4c6a-8cfd-9db3449fe58f
-- title:
--   Inverse Moment: child margins sharp
-- statement:
--   The Inverse Moment construction uses the child margins sharp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Basic.lean#L60-L73
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Basic.lean#L60-L73

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Basic
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment

theorem OAI.SevenEighths.InverseMoment.child_margins_sharp {F M Q Q' z c ell A t g theta V j delta eta : ℝ}
    (h : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hgt : -2 * eta ≤ g - theta)
    (hQ : Q' ≤ Q + decrease ell A t g theta V + 4 * eta) :
    c + delta - 5 * eta ≤
      childF F ell A t g theta V j delta -
      childM M ell A t g theta V j eta - Q' - z ∧
    c + 4 * delta - 7 * eta ≤
      4 * childF F ell A t g theta V j delta -
      3 * childM M ell A t g theta V j eta - 6 * z := by sorry
