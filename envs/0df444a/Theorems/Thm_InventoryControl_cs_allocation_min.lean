-- Prove2me | Theorems.Thm_InventoryControl_cs_allocation_min
-- name    : InventoryControl.cs_allocation_min
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:19:07.177719+00:00
-- url     : https://prove2.me/theorems/64c28148-c7b2-4812-8812-b4537b065ffd
-- title:
--   Sect. 10.1.1, p. 196: given $y_2$ and $D(L_2)$, the best feasible $y_1$ is $\min\{\hat y_1^*, y_2 - D(L_2)\}$
-- statement:
--   Let $S_1 = \hat y_1^{*}$ satisfy the fractile condition (10.8), with $e_1, e_2 \ge 0$,
--   $b_1 > 0$ and $\sigma > 0$. In a period in which installation 2 holds the echelon position
--   $y_2$ and the demand over the lead-time $L_2$ turns out to be $u$, installation 1 can realize
--   any position $y_1 \le y_2 - u$ (Eq. 10.1), and among these the cheapest is
--
--   $$ y_1 \;=\; \min\{S_1,\ y_2 - u\}: \qquad \tilde C_1\big(\min\{S_1, y_2 - u\}\big) \;\le\; \tilde C_1(y_1)
--      \quad\text{for every } y_1 \le y_2 - u. $$
--
--   If enough stock is available the unconstrained optimum $S_1$ is chosen; otherwise everything
--   available is passed on, because $\tilde C_1$ is convex and decreasing to the left of its
--   minimizer. This is the rule an echelon-stock order-up-to-$S_1$ policy implements, and the book
--   stresses that it does not depend on $y_2$: the optimal policy at installation 1 is determined
--   before anything is known about installation 2.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 196, Sect. 10.1.1: 'If y2 - D(L2) >= y-hat*1 we obtain the optimal solution if we have y1 = y-hat*1. But if y2 - D(L2) < y-hat*1, the best possible value of y1 is y1 = y2 - D(L2) due to the convexity of (10.6)'

import Definitions.Def_InventoryControl_clarkScarf

namespace InventoryControl

theorem cs_allocation_min (e1 e2 b1 mu sigma : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (hb : 0 < b1)
    (hs : 0 < sigma) (L1 : ℕ) (S1 : ℝ)
    (hS1 : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
      ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) = (e2 + b1) / (e1 + e2 + b1))
    (y2 u y1 : ℝ) (hy : y1 ≤ y2 - u) :
    csStage1Cost e1 e2 b1 mu sigma L1 (min S1 (y2 - u)) ≤ csStage1Cost e1 e2 b1 mu sigma L1 y1 := by sorry

end InventoryControl
