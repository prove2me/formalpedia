-- Prove2me | Theorems.Thm_LostSalesRQ_intersection_penalty_formula
-- name    : LostSalesRQ.intersection_penalty_formula
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:24:23.590208+00:00
-- url     : https://prove2.me/theorems/f65349f1-853b-43d1-9917-39e0350231a0
-- title:
--   Eq. (15): intersection penalties and the common cost
-- statement:
--   Fix $\mu>0$ and an integer $j\ge0$, and write $\delta_j=e_j-e_{j+1}$. Then
--   $$\delta_j=\frac{e_j(H_j+1)}{\mu+H_j+1}>0,\qquad a_j=\delta_j^{-1}-\mu=A_j\Big(1+\frac{v_j}{H_j+1}\Big),$$
--   and at the intersection penalty $a_j$ the neighboring base stocks have the common cost
--   $$L_j(a_j)=L_{j+1}(a_j)=H_j+1+\frac{v_j}{H_j+1}=j+1-\mu+\frac{\mu}{H_j+1}.$$
--
--   Raising the base-stock level from $j$ to $j+1$ trades extra holding cost $1-\mu\delta_j$ against a lost-sales saving $a\delta_j$; the intersection penalties are the endpoints used in Lemma 2(ii).
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Section 4.4.1, eq. (15) (p. 16); Appendix A.2 (p. A2).

import Definitions.Def_LostSalesRQ_poisson_functions

namespace LostSalesRQ

theorem intersection_penalty_formula (μ : ℝ) (hμ : 0 < μ) (j : ℕ) :
    lossFraction μ j - lossFraction μ (j + 1) =
        lossFraction μ j * (meanOnHand μ j + 1) / (μ + meanOnHand μ j + 1) ∧
    0 < lossFraction μ j - lossFraction μ (j + 1) ∧
    intersectionPenalty μ j =
        erlangNormalizer μ j * (1 + onHandVariance μ j / (meanOnHand μ j + 1)) ∧
    baseStockCost μ (intersectionPenalty μ j) j =
        baseStockCost μ (intersectionPenalty μ j) (j + 1) ∧
    baseStockCost μ (intersectionPenalty μ j) j =
        meanOnHand μ j + 1 + onHandVariance μ j / (meanOnHand μ j + 1) ∧
    baseStockCost μ (intersectionPenalty μ j) j =
        (j : ℝ) + 1 - μ + μ / (meanOnHand μ j + 1) := by sorry

end LostSalesRQ
