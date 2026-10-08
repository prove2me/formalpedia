-- Prove2me | Theorems.Thm_HarrisEOQ_Lot_cost_per_unit_eq
-- name    : HarrisEOQ.Lot.cost_per_unit_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:20:22.213474+00:00
-- url     : https://prove2.me/theorems/0d83229e-6466-4389-a6fd-330fde9c5306
-- title:
--   p. 948 — the interest charge per piece is (1/240M)(CX + S), and Y = interest + S/X + C
-- statement:
--   Let $M > 0$, and let $C$, $S$, $X$ be real numbers. Take one-tenth (the ten per cent annual charge) of the value $\tfrac12(CX + S)$ of the average stock and divide it by the $12M$ units used in a year. Then
--
--   1. the interest charge per piece equals
--   $$
--   \frac{\tfrac1{10}\cdot\tfrac12(CX+S)}{12M} = \frac{1}{240M}(CX + S);
--   $$
--   2. the cost per unit $Y(X) = \frac{1}{240M}(CX + S) + \frac SX + C$ is the interest charge per piece plus the set-up cost per piece $S/X$ plus the unit cost $C$.
--
--   This is the step that links Harris's verbal derivation to the display $Y$ whose minimization is the goal of the mission.
--
--   **Formalization Note** Only $M > 0$ is assumed: the identity is algebra away from $M = 0$, so the page's implicit $X > 0$, $C > 0$, $S > 0$ are not needed and are dropped.
-- source:
--   Harris, How many parts to make at once, Operations Research 38(6) (1990), p. 948, left column, fourth to sixth paragraphs and the display Y at the foot of the column

import Mathlib
import Definitions.Def_HarrisEOQ_Lot_Setting

namespace HarrisEOQ.Lot

theorem cost_per_unit_eq (M C S X : ℝ) (hM : 0 < M) :
    interestPerPiece M C S X = 1 / (240 * M) * (C * X + S) ∧
      costPerUnit M C S X = interestPerPiece M C S X + S / X + C := by sorry

end HarrisEOQ.Lot
