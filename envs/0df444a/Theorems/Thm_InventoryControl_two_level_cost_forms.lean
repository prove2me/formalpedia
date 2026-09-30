-- Prove2me | Theorems.Thm_InventoryControl_two_level_cost_forms
-- name    : InventoryControl.two_level_cost_forms
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:09:18.247706+00:00
-- url     : https://prove2.me/theorems/f4aded29-b5c2-4331-9fb3-3d5e0c895e47
-- title:
--   Eq. (9.6) and Eq. (9.9) are the same cost
-- statement:
--   In the two-level serial system with $Q_2 = kQ_1$, the cost written with installation holding
--   costs $h_1, h_2$,
--
--   $$ \big(h_1 + (k-1)h_2\big)\frac{Q_1}{2} + \Big(A_1 + \frac{A_2}{k}\Big)\frac{d}{Q_1}, $$
--
--   equals the cost written with echelon holding costs $e_1 = h_1 - h_2$, $e_2 = h_2$,
--
--   $$ (e_1 + ke_2)\frac{Q_1}{2} + \Big(A_1 + \frac{A_2}{k}\Big)\frac{d}{Q_1}, $$
--
--   for all $k \ne 0$ and $Q_1 \ne 0$.
--
--   The echelon stock of item 2 includes the stock of item 1, so charging $e_1$ on item 1's stock
--   and $e_2$ on item 2's echelon stock counts every unit's holding cost exactly once. The book
--   prefers the echelon form because its two terms have the same structure as the single-item
--   model, which is what allows the $N$-stage problem to be written as Eq. (9.17).
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, pp. 176-177, Sect. 9.2.1, Eq. (9.6), (9.9) and the sentence after (9.9): 'are the same, i.e., the cost expressions (9.6) and (9.9) are equivalent' (Problem 9.3)

import Definitions.Def_InventoryControl_serial

namespace InventoryControl

theorem two_level_cost_forms (d A1 A2 h1 h2 Q1 k : ℝ) (hk : k ≠ 0) (hQ : Q1 ≠ 0) :
    twoLevelCostInst d A1 A2 h1 h2 Q1 k = twoLevelCost d A1 A2 (h1 - h2) h2 Q1 k := by sorry

end InventoryControl
