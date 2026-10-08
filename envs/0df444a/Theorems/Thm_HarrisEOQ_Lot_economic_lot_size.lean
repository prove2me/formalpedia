-- Prove2me | Theorems.Thm_HarrisEOQ_Lot_economic_lot_size
-- name    : HarrisEOQ.Lot.economic_lot_size
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:20:36.644469+00:00
-- url     : https://prove2.me/theorems/97301d95-6c88-42f7-9498-297bf5ef4e3b
-- title:
--   p. 948 — for M, C, S > 0, X = √(240MS/C) is the unique minimizer over X > 0 of Y = (1/240M)(CX + S) + S/X + C
-- statement:
--   Let $M > 0$ be the number of units used per month, $C > 0$ the unit cost in dollars and $S > 0$ the set-up cost of an order in dollars. For a lot size $X > 0$ the whole cost of a unit is
--   $$
--   Y(X) = \frac{1}{240M}(CX + S) + \frac{S}{X} + C .
--   $$
--   Let $X^* = \sqrt{240MS/C}$. Then
--
--   1. $X^* > 0$, so $X^*$ is an admissible lot size;
--   2. $Y(X^*) \le Y(X)$ for every $X > 0$;
--   3. if $X > 0$ and $Y(X) = Y(X^*)$, then $X = X^*$.
--
--   In words, the value of $X$ that gives the minimum value to $Y$ is the square root of $240MS$ divided by $C$, and it is the only such value. This is the square-root (economic order quantity) formula, the main claim of the paper; Harris states it without proof.
--
--   **Formalization Note** The page does not state $M, C, S > 0$; they are implicit in the meaning of a usage rate, a price and a cost, and are added as hypotheses. Lot sizes range over the real numbers $X > 0$: in Lean $S/0 = 0$, so admitting $X = 0$ would make the statement false.
-- source:
--   Harris, How many parts to make at once, Operations Research 38(6) (1990), p. 948, the display Y (foot of the left column) and the sentence following it (top of the right column: "the value for X that will give the minimum value to Y, reduces to the square root of (240MS divided by C)")

import Mathlib
import Definitions.Def_HarrisEOQ_Lot_Setting

namespace HarrisEOQ.Lot

theorem economic_lot_size (M C S : ℝ) (hM : 0 < M) (hC : 0 < C) (hS : 0 < S) :
    0 < econLotSize M C S ∧
      (∀ X : ℝ, 0 < X → costPerUnit M C S (econLotSize M C S) ≤ costPerUnit M C S X) ∧
      (∀ X : ℝ, 0 < X → costPerUnit M C S X = costPerUnit M C S (econLotSize M C S) →
        X = econLotSize M C S) := by sorry

end HarrisEOQ.Lot
