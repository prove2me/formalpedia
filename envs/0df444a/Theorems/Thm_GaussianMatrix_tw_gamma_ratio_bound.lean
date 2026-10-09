-- Prove2me | Theorems.Thm_GaussianMatrix_tw_gamma_ratio_bound
-- name    : GaussianMatrix.tw_gamma_ratio_bound
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T08:27:55.346983+00:00
-- url     : https://prove2.me/theorems/80b3e2e5-a696-40c9-a525-b813ab2511c7
-- title:
--   Gamma-ratio bound $2^{\frac{k-r-1}2}\Gamma(\frac{k+1}2)/(\Gamma(\frac r2)\Gamma(k-r+1))\le(\frac{k+r}2)^{\frac{k-r+1}2}/(2\Gamma(k-r+1))$
-- statement:
--   Let $1\le r\le k$ be integers. Then
--   $$\frac{2^{(k-r-1)/2}\,\Gamma\!\big(\frac{k+1}{2}\big)}{\Gamma\!\big(\frac r2\big)\,\Gamma(k-r+1)}\;\le\;\frac{1}{2\,\Gamma(k-r+1)}\Big(\frac{k+r}{2}\Big)^{(k-r+1)/2},$$
--   where $\Gamma$ is Euler's Gamma function.
--
--   Equivalently, $2^{(k-r+1)/2}\,\Gamma(\frac{k+1}{2})/\Gamma(\frac r2)\le((k+r)/2)^{(k-r+1)/2}$. This is the deterministic step from Tropp–Webber's (B.5) to (B.6): it replaces the density constant of Edelman's bound by an elementary one. The proof writes $\Gamma(\frac{k+1}2)/\Gamma(\frac r2)=\prod_{i=0}^{k-r}\Gamma(\frac{r+i+1}{2})/\Gamma(\frac{r+i}{2})$, bounds each factor by $\sqrt{(r+i)/2}$ using Wendel–Gautschi $\Gamma(z+\frac12)\le z^{1/2}\Gamma(z)$ (a consequence of log-convexity of $\Gamma$), and then uses AM–GM in the paired form $(r+i)(k-i)\le((k+r)/2)^2$ to get $\prod_{i=0}^{k-r}(r+i)\le((k+r)/2)^{k-r+1}$.
--
--   **Formalization Note.** `Real.Gamma`; the powers are real powers with positive bases. Both sides are positive under the hypotheses.
-- source:
--   J. A. Tropp and R. J. Webber, arXiv:2306.12418, Appendix B, proof of Lemma B.3, the display between (B.5) and (B.6). It uses Γ(z+1/2) ≤ z^{1/2} Γ(z) (J. G. Wendel, Note on the gamma function, Amer. Math. Monthly 55 (1948) 563–564; TW ref. [59]) and (r+i)(k−i) ≤ ((k+r)/2)².

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem tw_gamma_ratio_bound {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) :
    2 ^ (((k : ℝ) - r - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
        / (Real.Gamma ((r : ℝ) / 2) * Real.Gamma ((k : ℝ) - r + 1))
      ≤ (((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2) / (2 * Real.Gamma ((k : ℝ) - r + 1)) := by
  sorry

end GaussianMatrix
