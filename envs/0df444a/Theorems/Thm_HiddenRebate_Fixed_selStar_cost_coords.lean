-- Prove2me | Theorems.Thm_HiddenRebate_Fixed_selStar_cost_coords
-- name    : HiddenRebate.Fixed.selStar_cost_coords
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:58.023925+00:00
-- url     : https://prove2.me/theorems/e59dbcf0-fe4d-4d9d-a9c9-a0731df82d55
-- title:
--   §5.1, p. 12 — in cost coordinates, A∗(xS, xW) = S iff xS ≤ xW
-- statement:
--   Let $r \in \mathbb R$ and let $A^*$ be the selection rule of (15). Evaluated at the truthful quotes $q = (x_S, x_W + r)$ of a cost pair $(x_S, x_W)$, the rule selects $S$ exactly when $S$ is the cheaper manufacturer:
--   $$A^*(x_S, x_W + r) = S \iff x_S \le x_W.$$
--
--   This is the translation of the selection rule from quote coordinates to cost coordinates; it is what makes the contract (15) select the efficient manufacturer (no distortion, eq. (18)) and gives the cost formula (19).
-- source:
--   Fan, Chen & Tang, Mechanism design for managing hidden rebates and inflated quotes of a procurement service provider, SSRN preprint 3514358, p. 12, §5.1

import Mathlib
import Definitions.Def_HiddenRebate_Fixed_Model

namespace HiddenRebate.Fixed

/-- §5.1, p. 12: in cost coordinates, `A∗(xS, xW) = S` iff `xS ≤ xW`. -/
theorem selStar_cost_coords (r : ℝ) (x : ℝ × ℝ) :
    (contractStar r).1 (quote r x) = Supplier.S ↔ x.1 ≤ x.2 := by sorry

end HiddenRebate.Fixed
