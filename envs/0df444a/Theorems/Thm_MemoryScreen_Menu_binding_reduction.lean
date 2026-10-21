-- Prove2me | Theorems.Thm_MemoryScreen_Menu_binding_reduction
-- name    : MemoryScreen.Menu.binding_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:00.316698+00:00
-- url     : https://prove2.me/theorems/e8722835-7edc-4847-944d-bd1930c6c514
-- title:
--   Proof of Proposition 1, p. 28 — binding IR and IC constraints
-- statement:
--   For any feasible menu with prices $(p_H,p_L)$, seller profit is bounded above by the reduced objective $\Phi(p_H,p_L)$ obtained by binding the low type's participation constraint and the high type's incentive constraint. The fees of the binding menu attain that bound:
--
--   $$\Pi(M)\le\Phi(p_H,p_L),\qquad\Pi(M^{\rm bind}(p_H,p_L))=\Phi(p_H,p_L).$$
--
--   At every optimal feasible menu, both of those constraints bind. This reduction connects the original limited-memory program (6) to the two-price expression printed in the proof of Proposition 1.
-- source:
--   Guo, The Mnemonomics of Contractual Screening, SSRN preprint 3930657 (2022-03-13), pp. 11, 28 (PDF 12, 29), §3.2.1 and proof of Proposition 1

import Mathlib
import Definitions.Def_MemoryScreen_Menu_Model

open MeasureTheory

namespace MemoryScreen.Menu

/-- Binding IR_L and IC_H,L reduce program (6) to the displayed objective in the proof of Proposition 1. -/
theorem binding_reduction (P : Params) (hS : P.Standing) :
    (∀ M : Menu, Feasible P M → profit P M ≤ reducedObj P M.pH M.pL) ∧
    (∀ pH pL : ℝ, profit P (bindingMenu P pH pL) = reducedObj P pH pL) ∧
    (∀ M : Menu, IsOptimal P M →
      EU P M.TL M.pL P.αL P.αL = 0 ∧
      EU P M.TL M.pL P.αH P.αL = EU P M.TH M.pH P.αH P.αH) := by sorry

end MemoryScreen.Menu
