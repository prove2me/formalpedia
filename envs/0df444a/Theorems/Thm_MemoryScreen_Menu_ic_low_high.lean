-- Prove2me | Theorems.Thm_MemoryScreen_Menu_ic_low_high
-- name    : MemoryScreen.Menu.ic_low_high
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:01.879923+00:00
-- url     : https://prove2.me/theorems/5108cb53-7ed9-4765-86f7-1e8631a03da9
-- title:
--   Proof of Proposition 1, p. 28 — low-type incentive constraint
-- statement:
--   Assume the model's standing conditions and let $p_H<p_L$. For the menu whose fees bind the low type's participation constraint and the high type's incentive constraint, all four participation and incentive inequalities of program (6) hold:
--
--   $$M^{\rm bind}(p_H,p_L)\in\mathcal F.$$
--
--   In particular, the low type does not gain by deviating to the high-type contract. The high and low contracts carry their own stage-two beliefs in this comparison.
-- source:
--   Guo, The Mnemonomics of Contractual Screening, SSRN preprint 3930657 (2022-03-13), p. 28 (PDF 29), proof of Proposition 1, IC_L,H paragraph

import Mathlib
import Definitions.Def_MemoryScreen_Menu_Model

open MeasureTheory

namespace MemoryScreen.Menu

/-- The low type's downward IC constraint follows when the high marginal price is lower. -/
theorem ic_low_high (P : Params) (hS : P.Standing) (pH pL : ℝ)
    (hprice : pH < pL) : Feasible P (bindingMenu P pH pL) := by sorry

end MemoryScreen.Menu
