-- Prove2me | Theorems.Thm_InventoryControl_two_level_opt_k
-- name    : InventoryControl.two_level_opt_k
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:10:28.972481+00:00
-- url     : https://prove2.me/theorems/ea375955-455e-42b7-8d1c-3d300db544ca
-- title:
--   Eq. (9.12)-(9.13): $C(k)^2$ is convex in $k$ and minimized at $k^* = \sqrt{A_2e_1/(A_1e_2)}$
-- statement:
--   In the two-level serial system with $d, A_1, A_2, e_1, e_2 > 0$, the optimal cost for a given
--   ratio $k > 0$ satisfies
--
--   $$ C(k)^2 \;=\; 2d\Big(A_1e_1 + A_2e_2 + A_1e_2\,k + \frac{A_2e_1}{k}\Big), $$
--
--   this function of $k$ is convex on $(0, \infty)$, and, disregarding that $k$ has to be an
--   integer, $C(k)$ is minimized over $k > 0$ at
--
--   $$ k^{*} \;=\; \sqrt{\frac{A_2e_1}{A_1e_2}} . $$
--
--   The square of the cost separates into a constant, a term linear in $k$ and a term
--   proportional to $1/k$, so the minimization over $k$ is once more an EOQ-shaped problem. The
--   value $k^{*}$ does not depend on the demand $d$, which the book uses in Sect. 9.3.2 to carry
--   the same ratio over to time-varying demand.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 177, Sect. 9.2.1, Eq. (9.12) and Eq. (9.13)

import Definitions.Def_InventoryControl_serial

namespace InventoryControl

theorem two_level_opt_k (d A1 A2 e1 e2 : ℝ) (hd : 0 < d) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (he1 : 0 < e1) (he2 : 0 < e2) :
    (∀ k : ℝ, 0 < k → twoLevelOptCost d A1 A2 e1 e2 k ^ 2
        = 2 * d * (A1 * e1 + A2 * e2 + A1 * e2 * k + A2 * e1 / k))
      ∧ ConvexOn ℝ (Set.Ioi 0) (fun k => twoLevelOptCost d A1 A2 e1 e2 k ^ 2)
      ∧ ∀ k : ℝ, 0 < k →
          twoLevelOptCost d A1 A2 e1 e2 (Real.sqrt (A2 * e1 / (A1 * e2)))
            ≤ twoLevelOptCost d A1 A2 e1 e2 k := by sorry

end InventoryControl
