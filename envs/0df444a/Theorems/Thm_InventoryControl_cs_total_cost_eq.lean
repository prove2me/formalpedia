-- Prove2me | Theorems.Thm_InventoryControl_cs_total_cost_eq
-- name    : InventoryControl.cs_total_cost_eq
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:19:41.819625+00:00
-- url     : https://prove2.me/theorems/3646c8e8-2945-49e9-88fe-888b69fe98e0
-- title:
--   Eq. (10.9): the expected cost of the order-up-to-$S_1$ rule is $\hat C_2(y_2)$
-- statement:
--   When installation 2 holds the echelon position $y_2$ and installation 1 realizes
--   $y_1 = \min\{S_1, y_2 - D(L_2)\}$, the expected total reallocated cost
--   $\mathbb{E}\big[\tilde C_2(y_2) + \tilde C_1(\min\{S_1, y_2 - D(L_2)\})\big]$ equals
--
--   $$ \hat C_2(y_2) \;=\; h_2(y_2 - \mu_2') + \hat C_1(S_1) + \int_{y_2 - S_1}^{\infty}\big[\hat C_1(y_2 - u) - \hat C_1(S_1)\big]\,\frac{1}{\sigma_2'}\varphi\!\Big(\frac{u - \mu_2'}{\sigma_2'}\Big)\mathrm{d}u, $$
--
--   for every $y_2$, every level $S_1$ and $\sigma > 0$, with $\mu_2' = L_2\mu$ and
--   $\sigma_2' = \sqrt{L_2}\,\sigma$.
--
--   The last term is the book's "shortage cost at installation 2 induced by its inability to
--   deliver on time to installation 1": on the event $D(L_2) > y_2 - S_1$ installation 1 receives
--   only $y_2 - D(L_2)$ instead of $S_1$. The identity holds for any $S_1$; it is the evaluation of
--   a piecewise expectation, and it is what makes $\hat C_2$ computable from the tabulated loss
--   function.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 196, Sect. 10.1.1, Eq. (10.9)

import Definitions.Def_InventoryControl_clarkScarf

namespace InventoryControl

theorem cs_total_cost_eq (e1 e2 b1 mu sigma : ℝ) (hs : 0 < sigma) (L1 L2 : ℕ) (S1 y2 : ℝ) :
    ∫ u, (csStage2Cost e2 mu L2 y2 + csStage1Cost e1 e2 b1 mu sigma L1 (min S1 (y2 - u)))
        ∂(csDemand mu sigma L2)
      = csTotalCost e1 e2 b1 mu sigma L1 L2 S1 y2 := by sorry

end InventoryControl
