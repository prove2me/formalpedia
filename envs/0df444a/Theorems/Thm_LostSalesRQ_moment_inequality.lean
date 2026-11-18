-- Prove2me | Theorems.Thm_LostSalesRQ_moment_inequality
-- name    : LostSalesRQ.moment_inequality
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:31:01.784698+00:00
-- url     : https://prove2.me/theorems/6ef33493-2494-4fdc-843a-5e9252aa7feb
-- title:
--   Lemma H.1: moment inequality
-- statement:
--   Fix an integer $j\ge1$ and $\mu\ge j$. With $H_j$, $v_j$, the intersection penalty $a_j$ and the common cost $L_j(a_j)$, set
--   $$\vartheta=\frac{v_j}{\mu},\qquad\tilde H_j=H_j-\frac{v_j}{H_j+1},\qquad\kappa=\frac{\tilde H_j}{L_j(a_j)} .$$
--   Then
--   $$\mathcal Z=\frac{2\vartheta}{7}-\kappa^2>0\qquad\text{and}\qquad L_j(a_j)>3\tilde H_j .$$
--
--   This relation between the mean and variance of on-hand inventory bounds the penalty available at the intersection in Lemma H.2.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Lemma H.1, eq. (H.2) (p. A15), with the notation of Appendix H (p. A14).

import Definitions.Def_LostSalesRQ_poisson_functions

namespace LostSalesRQ

theorem moment_inequality (μ : ℝ) (j : ℕ) (hj : 1 ≤ j) (hμj : (j : ℝ) ≤ μ) :
    0 < 2 * (onHandVariance μ j / μ) / 7 -
        ((meanOnHand μ j - onHandVariance μ j / (meanOnHand μ j + 1)) /
          baseStockCost μ (intersectionPenalty μ j) j) ^ 2 ∧
    3 * (meanOnHand μ j - onHandVariance μ j / (meanOnHand μ j + 1)) <
      baseStockCost μ (intersectionPenalty μ j) j := by sorry

end LostSalesRQ
