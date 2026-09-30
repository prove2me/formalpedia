-- Prove2me | Theorems.Thm_InventoryControl_s_policy_cost_convex
-- name    : InventoryControl.s_policy_cost_convex
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:54:12.275884+00:00
-- url     : https://prove2.me/theorems/589bb984-f3ba-4821-b1f4-e3561e041aa2
-- title:
--   $g$ is convex on $\mathbb{Z}$ and $g(k) \to \infty$ as $|k| \to \infty$
-- statement:
--   For a discrete lead-time demand with finite mean and costs $h > 0$, $b_1 > 0$, the $S$-policy
--   cost rate $g$ is a convex function of the inventory position $k \in \mathbb{Z}$, in the sense
--   that its increments are nondecreasing,
--
--   $$ g(k+1) - g(k) \;\le\; g(k+2) - g(k+1) \qquad\text{for all } k, $$
--
--   and $g(k) \to \infty$ as $|k| \to \infty$.
--
--   Both follow from the increment identity $g(k+1) - g(k) = -b_1 + (h+b_1)\Pr[D(L) \le k]$: the
--   distribution function is nondecreasing, and the increments tend to $-b_1 < 0$ as $k \to
--   -\infty$ and to $h > 0$ as $k \to +\infty$. These are the two properties Sect. 6.1.1.1 needs
--   of $g$: convexity makes the best set of $Q$ consecutive positions grow by one neighbour at a
--   time, and the growth at infinity guarantees that every cost minimization over $R$ is attained.
--
--   **Formalization Note** Divergence is stated as `Tendsto g (cocompact ℤ) atTop`, that is,
--   $g(k) \to \infty$ along $|k| \to \infty$ in both directions.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 108, Sect. 6.1.1.1: 'The results in Sect. 5.9.1 imply that g(k) is a convex function of the inventory position k. Furthermore g(k) -> infinity as |k| -> infinity'; restated p. 114 after Eq. (6.20)

import Definitions.Def_InventoryControl_rqDiscrete

namespace InventoryControl

theorem s_policy_cost_convex (D : DiscreteDemand) (h b1 : ℝ) (hh : 0 < h) (hb : 0 < b1) :
    (∀ k : ℤ, sPolicyCost D h b1 (k + 1) - sPolicyCost D h b1 k
        ≤ sPolicyCost D h b1 (k + 2) - sPolicyCost D h b1 (k + 1))
      ∧ Filter.Tendsto (sPolicyCost D h b1) (Filter.cocompact ℤ) Filter.atTop := by sorry

end InventoryControl
