-- Prove2me | Theorems.Thm_InventoryControl_cs_cost_reallocation
-- name    : InventoryControl.cs_cost_reallocation
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:17:30.530011+00:00
-- url     : https://prove2.me/theorems/1981804a-6b7a-41a7-9493-d36671f9095b
-- title:
--   Eq. (10.4)-(10.5): reallocating $-h_2y_1$ to stage 1 does not change the total cost
-- statement:
--   For every echelon position $y_2$ of installation 2 and realized position $y_1$ of
--   installation 1, the sum of the period costs (10.2) and (10.3),
--
--   $$ h_2\,(y_2 - \mu_2') - h_2\,y_1 \;+\; h_1\,(y_1 - \mu_1'') + (h_1 + b_1)\,\mathbb{E}\big(y_1 - D(L_1+1)\big)^{-}, $$
--
--   equals the sum of the reallocated costs $\tilde C_2(y_2) = h_2(y_2 - \mu_2')$ and
--   $\tilde C_1(y_1) = e_1y_1 - h_1\mu_1'' + (h_1 + b_1)\,\mathbb{E}(y_1 - D(L_1+1))^{-}$, because
--   $h_1 - h_2 = e_1$.
--
--   The reallocation is what decouples the two installations: $\tilde C_2$ no longer depends on
--   $y_1$, and $\tilde C_1$ depends on $y_2$ only through the constraint $y_1 \le y_2 - D(L_2)$.
--   The book remarks that the transferred term is normally negative, so $\tilde C_1$ may be
--   negative, as it is in Example 10.1.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 195, Sect. 10.1.1, Eq. (10.4), Eq. (10.5) and 'Of course this reallocation does not affect the total costs'

import Definitions.Def_InventoryControl_clarkScarf

namespace InventoryControl

theorem cs_cost_reallocation (e1 e2 b1 mu sigma : ℝ) (hs : 0 < sigma) (L1 L2 : ℕ) (y2 y1 : ℝ) :
    csPeriodCost e1 e2 b1 mu sigma L1 L2 y2 y1
      = csStage2Cost e2 mu L2 y2 + csStage1Cost e1 e2 b1 mu sigma L1 y1 := by sorry

end InventoryControl
