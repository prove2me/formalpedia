-- Prove2me | Theorems.Thm_InventoryControl_cs_stage1_period_cost
-- name    : InventoryControl.cs_stage1_period_cost
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:16:58.4007+00:00
-- url     : https://prove2.me/theorems/59a41fbb-c598-4c5e-837e-677ea25c7b9d
-- title:
--   Eq. (10.3): $h_1\mathbb{E}(y_1 - D)^+ + b_1\mathbb{E}(y_1 - D)^- = h_1(y_1 - \mu_1'') + (h_1 + b_1)\mathbb{E}(y_1 - D)^-$
-- statement:
--   The average period cost at installation 1 in period $t + L_2 + L_1$, evaluated after the period
--   demand, is the holding cost on the positive part of the inventory level $y_1 - D(L_1+1)$ plus
--   the shortage cost on its negative part, and it can be written with a single expectation: for
--   every $y_1$ and $\sigma > 0$,
--
--   $$ h_1\,\mathbb{E}\big(y_1 - D(L_1+1)\big)^{+} + b_1\,\mathbb{E}\big(y_1 - D(L_1+1)\big)^{-}
--      \;=\; h_1\,(y_1 - \mu_1'') + (h_1 + b_1)\,\mathbb{E}\big(y_1 - D(L_1+1)\big)^{-}, $$
--
--   with $\mu_1'' = (L_1+1)\mu$ the mean demand over $L_1 + 1$ periods and $h_1 = e_1 + e_2$.
--
--   The identity is $x^{+} = x + x^{-}$ integrated against the demand law, using that $D(L_1+1)$
--   has mean $\mu_1''$. It is the standard argument of Sect. 5.3.2 applied to installation 1: the
--   realized position $y_1$ is independent of the demand in the $L_1 + 1$ periods that follow, so
--   the inventory level after the period demand is $y_1 - D(L_1+1)$.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 194, Sect. 10.1.1, Eq. (10.3)

import Definitions.Def_InventoryControl_clarkScarf

namespace InventoryControl

theorem cs_stage1_period_cost (e1 e2 b1 mu sigma : ℝ) (hs : 0 < sigma) (L1 : ℕ) (y1 : ℝ) :
    (e1 + e2) * (∫ x, max (y1 - x) 0 ∂(csDemand mu sigma (L1 + 1)))
        + b1 * (∫ x, max (x - y1) 0 ∂(csDemand mu sigma (L1 + 1)))
      = (e1 + e2) * (y1 - (L1 + 1) * mu)
        + (e1 + e2 + b1) * ∫ x, max (x - y1) 0 ∂(csDemand mu sigma (L1 + 1)) := by sorry

end InventoryControl
