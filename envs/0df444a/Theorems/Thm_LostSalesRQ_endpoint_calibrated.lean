-- Prove2me | Theorems.Thm_LostSalesRQ_endpoint_calibrated
-- name    : LostSalesRQ.endpoint_calibrated
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:32:01.997636+00:00
-- url     : https://prove2.me/theorems/7196288d-f285-4fe7-a119-a00ec6204059
-- title:
--   Lemma 2(iii): comparisons at calibrated penalties above mean demand
-- statement:
--   Fix $\mu>0$. For every integer $j\ge\mu$ write $\widehat a_j=\alpha_\mu(A_j)$, where $A_j=1/e_j$ is the Erlang normalizer. Then
--   $$\max\{L_j(\widehat a_j),L_{j+1}(\widehat a_j)\}<\sqrt2\,B_\mu(A_j)\le\sqrt2\,\mathcal L_\mu(\widehat a_j),$$
--   and the sequence $\widehat a_j$ ($j\ge\mu$) increases to infinity.
--
--   Consecutive calibrated penalties bracket intervals on which a single base-stock level satisfies the $\sqrt2$ comparison, covering every penalty $a\ge\widehat a_S$ with $S\ge\mu$.
--
--   **Formalization Note** The weight is `erlangNormalizer μ j` $=F_j(\mu)/p_j(\mu)$, which equals $1/e_j$. Strict increase is stated on $\{j:j\ge\mu\}$ and divergence along all $j$.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Lemma 2(iii), eq. (19) (p. 17); proof in Appendix F (pp. A10-A12).

import Definitions.Def_LostSalesRQ_lower_curve
import Definitions.Def_LostSalesRQ_poisson_process

namespace LostSalesRQ

theorem endpoint_calibrated (μ : ℝ) (hμ : 0 < μ) :
    (∀ j : ℕ, μ ≤ (j : ℝ) →
      max (baseStockCost μ (calibratedPenalty μ (erlangNormalizer μ j)) j)
          (baseStockCost μ (calibratedPenalty μ (erlangNormalizer μ j)) (j + 1)) <
        Real.sqrt 2 * rankBound μ (erlangNormalizer μ j) ∧
      Real.sqrt 2 * rankBound μ (erlangNormalizer μ j) ≤
        Real.sqrt 2 * lowerCurve μ (calibratedPenalty μ (erlangNormalizer μ j))) ∧
    StrictMonoOn (fun j : ℕ => calibratedPenalty μ (erlangNormalizer μ j))
      {j : ℕ | μ ≤ (j : ℝ)} ∧
    Filter.Tendsto (fun j : ℕ => calibratedPenalty μ (erlangNormalizer μ j))
      Filter.atTop Filter.atTop := by sorry

end LostSalesRQ
