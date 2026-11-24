-- Prove2me | Theorems.Thm_LearnThenTest_clt_pvalue_asymptotically_valid
-- name    : LearnThenTest.clt_pvalue_asymptotically_valid
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T00:09:10.002899+00:00
-- url     : https://prove2.me/theorems/85795e9d-e658-406f-a760-d756bc8131a1
-- title:
--   Proposition B.1: CLT p-values are asymptotically valid
-- statement:
--   Let $L_1,L_2,\dots$ be i.i.d. real losses with finite mean $R=\mathbb E[L_1]$ and finite, positive variance. Let $\alpha\le R$; this covers the null hypothesis $\mathcal H_j:R(\lambda_j)>\alpha$ and its boundary $R=\alpha$. For each $n$, let $\hat R_n=\frac1n\sum_{i=1}^nL_i$ and let $\hat\sigma_n=\Big(\big((L_1-\hat R_n)^2+\dots+(L_n-\hat R_n)^2\big)/(n-1)\Big)^{1/2}$ be the empirical standard deviation, and let $\Phi$ be the standard normal distribution function. Then the CLT p-value
--
--   $$p^{\mathrm{CLT}}_n=1-\Phi\Big(\frac{\alpha-\hat R_n}{\hat\sigma_n/\sqrt n}\Big)$$
--
--   is asymptotically valid: for every $u\in[0,1]$,
--
--   $$\limsup_{n\to\infty}\mathbb P(p^{\mathrm{CLT}}_n\le u)\le u.$$
--
--   **Formalization Note** The paper prints $\hat\sigma_n=\big(\sum_i(L_i-\hat R_n)^2\big)^{1/2}/(n-1)$, which is the empirical standard deviation it names divided by $\sqrt{n-1}$; the statement uses the empirical standard deviation. The null is taken closed, $\alpha\le R$, which strengthens the printed $\alpha<R$. Under the strict null alone, $p^{\mathrm{CLT}}_n\to1$ in probability by the law of large numbers, and the statement would hold for any consistent or even wrongly scaled $\hat\sigma$. At $R=\alpha$ the central limit theorem gives $\mathbb P(p^{\mathrm{CLT}}_n\le u)\to u$, which is the content the paper intends. The hypothesis of positive variance is added because the formula is undefined when $\hat\sigma_n=0$. With zero variance, $\hat\sigma_n=0$ almost surely; with positive variance, the event $\hat\sigma_n=0$ has probability tending to $0$. On that event Lean evaluates the quotient as $0$.
-- source:
--   Angelopoulos, Bates, Candès, Jordan and Lei, Learn then Test: Calibrating Predictive Algorithms to Achieve Risk Control, arXiv:2110.01052v5 (2022), Appendix B, Proposition B.1, p. 21; proof in Appendix C, p. 22

import Mathlib
import Definitions.Def_LearnThenTest_Basic

open MeasureTheory ProbabilityTheory Filter

namespace LearnThenTest

theorem clt_pvalue_asymptotically_valid {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (L : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (L i))
    (hind : iIndepFun L P) (hident : ∀ i, IdentDistrib (L i) (L 0) P P)
    (hL2 : MemLp (L 0) 2 P) (hvar : 0 < variance (L 0) P) (α : ℝ)
    (hnull : α ≤ ∫ ω, L 0 ω ∂P) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1,
      limsup (fun n : ℕ => P {ω | cltPValue α (fun i : Fin n => L i ω) ≤ u}) atTop ≤
        ENNReal.ofReal u := by sorry

end LearnThenTest
