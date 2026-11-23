-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_coefficient_estimates_at_251
-- name    : GrothendieckLB.Supplement.cq_coefficient_estimates_at_251
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T15:48:38.365869+00:00
-- url     : https://prove2.me/theorems/85d1e742-cab7-4391-b0b8-d407a66b4bba
-- title:
--   Certified cubic–quintic coefficient estimates at the degree-251 cutoff
-- statement:
--   Let $b_m$ be the Taylor coefficients of the cubic–quintic correlation with parameters $\eta=0.136419125$, $s_3=0.34101124$ and $s_5=0.05276111$. The linear coefficient and the next 125 odd coefficients satisfy
--   $$
--   b_1\ge0.881573822049,\qquad
--   \sum_{\substack{3\le m\le251\\m\ {\rm odd}}}|b_m|\le0.000011328860.
--   $$
--   The remaining odd coefficients are absolutely summable, with
--   $$
--   \sum_{\substack{m\ge253\\m\ {\rm odd}}}|b_m|
--   \le\frac{14.443}{\sqrt{10\cdot251^5}}.
--   $$
--   The first two estimates are the finite coefficient bounds of Proposition 6.3. For the last estimate, Lemma 6.2 applies Cauchy–Schwarz to the weighted coefficients $m^3b_m$ and uses the certified bound $\|D^3 H\|_{L^2(\mathbb T)}<14.443$.
-- source:
--   Saha, Li, Xue, Chaudhuri, Klivans, Kothari and Meka, New Lower and Upper Bounds for the Grothendieck Constant, https://arxiv.org/pdf/2608.11158v2, equation (7) (p. 16), Lemma 6.2, Proposition 6.3 and equations (25)–(28) (pp. 20–21), Appendix C.

import Definitions.Def_GrothendieckLB_taylorCoeff
import Definitions.Def_GrothendieckLB_Supplement_cqCorr

namespace GrothendieckLB.Supplement

theorem cq_coefficient_estimates_at_251 :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    let b := fun m : ℕ => GrothendieckLB.taylorCoeff m H
    0.881573822049 ≤ b 1 ∧
      (∑ j ∈ Finset.range 125, |b (2 * j + 3)|) ≤ 0.000011328860 ∧
      Summable (fun j : ℕ => |b (2 * j + 253)|) ∧
      (∑' j : ℕ, |b (2 * j + 253)|) ≤ 14.443 / Real.sqrt (10 * (251 : ℝ) ^ 5) := by sorry

end GrothendieckLB.Supplement
