-- Prove2me | Theorems.Thm_LostSalesRQ_intersection_penalty_bound
-- name    : LostSalesRQ.intersection_penalty_bound
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:31:14.930337+00:00
-- url     : https://prove2.me/theorems/25a7bd28-c9ed-451d-a1b6-3116aac76141
-- title:
--   Lemma H.2: the penalty at the intersection
-- statement:
--   For an integer $j\ge1$ and $\mu\ge\max\{j,3\}$, with $\sigma_H=1-\dfrac{5L_j(a_j)^2}{28\mu}$,
--   $$\sigma_H>0\qquad\text{and}\qquad a_j>\frac{L_j(a_j)}{2}+\frac{L_j(a_j)^2}{4\sigma_H}.$$
--
--   The intersection penalty is large enough to pay for the largest stockout aging contribution at the rank weight chosen in Lemma 2(ii).
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Lemma H.2, eq. (H.3) (p. A16).

import Definitions.Def_LostSalesRQ_poisson_functions

namespace LostSalesRQ

theorem intersection_penalty_bound (μ : ℝ) (j : ℕ) (hj : 1 ≤ j) (hμj : (j : ℝ) ≤ μ)
    (hμ3 : 3 ≤ μ) :
    0 < 1 - 5 * baseStockCost μ (intersectionPenalty μ j) j ^ 2 / (28 * μ) ∧
    baseStockCost μ (intersectionPenalty μ j) j / 2 +
        baseStockCost μ (intersectionPenalty μ j) j ^ 2 /
          (4 * (1 - 5 * baseStockCost μ (intersectionPenalty μ j) j ^ 2 / (28 * μ))) <
      intersectionPenalty μ j := by sorry

end LostSalesRQ
