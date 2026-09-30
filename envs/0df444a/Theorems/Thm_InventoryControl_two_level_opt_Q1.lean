-- Prove2me | Theorems.Thm_InventoryControl_two_level_opt_Q1
-- name    : InventoryControl.two_level_opt_Q1
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:09:54.801312+00:00
-- url     : https://prove2.me/theorems/eb79ba85-fda1-45cc-83d2-dd4303ca05a1
-- title:
--   Eq. (9.10)-(9.11): for a given $k$, $Q_1 = \sqrt{2(A_1 + A_2/k)d/(e_1 + ke_2)}$ and $C(k) = \sqrt{2(A_1 + A_2/k)d(e_1 + ke_2)}$
-- statement:
--   In the two-level serial system with final demand $d > 0$, ordering costs $A_1, A_2 > 0$,
--   echelon holding costs $e_1, e_2 > 0$ and a given ratio $k > 0$, the batch quantity of item 1
--   that minimizes the cost (9.9) over $Q_1 > 0$ is
--
--   $$ Q_1 \;=\; \sqrt{\frac{2(A_1 + A_2/k)\,d}{e_1 + ke_2}}, $$
--
--   and the resulting cost is
--
--   $$ C(k) \;=\; \sqrt{2\,(A_1 + A_2/k)\,d\,(e_1 + ke_2)}. $$
--
--   Both are the classical EOQ formulas (4.3)-(4.4) with the ordering cost $A$ replaced by
--   $A_1' = A_1 + A_2/k$ (Eq. 9.14) and the holding cost $h$ by $h_1' = e_1 + ke_2$ (Eq. 9.15), which
--   is how the book explains them; they are also the modified parameters that Blackburn and
--   Millen's sequential heuristic of Sect. 9.3.2 feeds to the Wagner-Whitin algorithm.
--
--   **Formalization Note** The optimal $Q_1$ is `eoq (A1 + A2/k) d (e1 + k e2)` from the chapter 4
--   definitions, and the claim reduces to the published `eoq_optimal` and `eoq_cost_at_eoq`.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 177, Sect. 9.2.1, Eq. (9.10) and Eq. (9.11)

import Definitions.Def_InventoryControl_serial

namespace InventoryControl

theorem two_level_opt_Q1 (d A1 A2 e1 e2 k Q1 : ℝ) (hd : 0 < d) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (he1 : 0 < e1) (he2 : 0 < e2) (hk : 0 < k) (hQ : 0 < Q1) :
    twoLevelCost d A1 A2 e1 e2 (eoq (A1 + A2 / k) d (e1 + k * e2)) k
        ≤ twoLevelCost d A1 A2 e1 e2 Q1 k
      ∧ twoLevelCost d A1 A2 e1 e2 (eoq (A1 + A2 / k) d (e1 + k * e2)) k
          = twoLevelOptCost d A1 A2 e1 e2 k := by sorry

end InventoryControl
