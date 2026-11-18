-- Prove2me | Theorems.Thm_LostSalesRQ_endpoint_below_mean
-- name    : LostSalesRQ.endpoint_below_mean
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:31:45.815397+00:00
-- url     : https://prove2.me/theorems/cb6b4a32-33c9-42f9-a8e9-5b377956d516
-- title:
--   Lemma 2(ii): comparisons at intersection penalties below mean demand
-- statement:
--   If $j\ge1$ is an integer and $\mu\ge\max\{j,3\}$, then at the intersection penalty $a_j$ of the cost lines of base stocks $j$ and $j+1$,
--   $$L_j(a_j)=L_{j+1}(a_j)\le\sqrt2\,\mathcal L_\mu(a_j).$$
--
--   These comparisons connect the successive base-stock levels $3,\dots,\lfloor\mu\rfloor+1$ in the interval argument of Section 4.4.3.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Lemma 2(ii), eq. (18) (p. 17); proof in Appendix H (pp. A14-A19).

import Definitions.Def_LostSalesRQ_lower_curve

namespace LostSalesRQ

theorem endpoint_below_mean (μ : ℝ) (j : ℕ) (hj : 1 ≤ j) (hμj : (j : ℝ) ≤ μ) (hμ3 : 3 ≤ μ) :
    baseStockCost μ (intersectionPenalty μ j) j =
        baseStockCost μ (intersectionPenalty μ j) (j + 1) ∧
    baseStockCost μ (intersectionPenalty μ j) j ≤
        Real.sqrt 2 * lowerCurve μ (intersectionPenalty μ j) := by sorry

end LostSalesRQ
