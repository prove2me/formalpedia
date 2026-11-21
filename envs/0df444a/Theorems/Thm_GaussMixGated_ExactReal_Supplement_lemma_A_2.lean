-- Prove2me | Theorems.Thm_GaussMixGated_ExactReal_Supplement_lemma_A_2
-- name    : GaussMixGated.ExactReal.Supplement.lemma_A_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T18:08:39.959167+00:00
-- url     : https://prove2.me/theorems/3cb4d814-d94f-45ef-a1b3-1257235c8009
-- title:
--   Lemma A.2 — fixed-frame perturbation (corrected: nonnegative tolerance)
-- statement:
--   Let $t\ge2$ be an integer, $N\ge\max\{2,t\}$ real and $0\le h\le1$. Let $\ell$ range over any finite set of terms, and let term $\ell$ have $r_\ell\le t$ factors, real coefficient $c_\ell$ and factor values $x_{\ell j},\widehat x_{\ell j}$. Assume $\sum_\ell|c_\ell|\le N^{2t}$, $|x_{\ell j}|\le N$ and $|\widehat x_{\ell j}-x_{\ell j}|\le h$. For $F(x)=\sum_\ell c_\ell\prod_{j=1}^{r_\ell}x_{\ell j}$, both bounds hold:
--   $$|F(x)|\le N^{3t},\qquad |F(\widehat x)-F(x)|\le N^{4t}h.$$
--   The term set may be empty and zero-factor products equal one. Factors may repeat and satisfy no independence condition. This estimate supplies the fixed-frame perturbation control in the precision budget for Theorem A.1.
--
--   Differences from the source:
--   - correction: the printed condition |xhat-x| ≤ h ≤ 1 permits negative h when every product is empty → the tolerance also satisfies 0 ≤ h; reason: with one empty product, coefficient 1, N=t=2 and h=-1 every printed assumption holds but the error conclusion is 0 ≤ -256; the added condition corrects exactly this empty-factor defect
--   - encoding: a finite sum of products with at most t factors per term → a finite index type and dependent factor types Fin (r l), allowing empty products and repeated values; reason: this represents all finite expressions with the same coefficient and factor bounds
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, Lemma A.2, PDF p. 34 (printed p. 32)

import Mathlib

namespace GaussMixGated.ExactReal.Supplement

/-- Lemma A.2, PDF p. 34 (printed p. 32). The tolerance is nonnegative.
Correction at empty products: with N=t=2, h=-1 and one constant term c=1, all printed
factor conditions are vacuous but the printed error bound reads 0 ≤ -256. -/
theorem lemma_A_2 {ι : Type*} [Fintype ι] (N : ℝ) (t : ℕ) (h : ℝ)
    (r : ι → ℕ) (c : ι → ℝ) (x xhat : (l : ι) → Fin (r l) → ℝ)
    (hN2 : 2 ≤ N) (hNt : (t : ℝ) ≤ N) (ht : 2 ≤ t)
    (hr : ∀ l, r l ≤ t) (hc : ∑ l, |c l| ≤ N ^ (2 * t))
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hx : ∀ l j, |x l j| ≤ N) (hxh : ∀ l j, |xhat l j - x l j| ≤ h) :
    |∑ l, c l * ∏ j, x l j| ≤ N ^ (3 * t) ∧
      |(∑ l, c l * ∏ j, xhat l j) - (∑ l, c l * ∏ j, x l j)| ≤
        N ^ (4 * t) * h := by sorry

end GaussMixGated.ExactReal.Supplement
