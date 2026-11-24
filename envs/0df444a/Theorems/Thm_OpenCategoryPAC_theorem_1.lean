-- Prove2me | Theorems.Thm_OpenCategoryPAC_theorem_1
-- name    : OpenCategoryPAC.theorem_1
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:23:27.886811+00:00
-- url     : https://prove2.me/theorems/27d5a034-cc0d-434b-92b6-bde847ac4fd3
-- title:
--   Theorem 1 (as proved): PAC guarantee on the alien detection rate
-- statement:
--   Let $\mu_0$ (nominal) and $\mu_a$ (alien) be the anomaly-score laws, with continuous CDFs $F_0$ and $F_a$, let $0<\alpha\le1$, and let the mixture score law be $\mu_m=(1-\alpha)\mu_0+\alpha\mu_a$. Let $S_0$ consist of $n$ i.i.d. draws from $\mu_0$ and, independently, $S_m$ of $n$ i.i.d. draws from $\mu_m$. Let $q>0$, $\epsilon\in(0,1-q)$ and $\delta\in(0,1)$, and suppose
--
--   $$n>\frac12\ln\frac{2}{1-\sqrt{1-\delta}}\left(\frac1\epsilon\right)^2\left(\frac{2-\alpha}{\alpha}\right)^2.$$
--
--   Let $\eta=q+\epsilon$. Then, with probability at least $1-\delta$ over the draw of $S_0$ and $S_m$, if Algorithm 1 returns a threshold $\hat\tau_q=\max\{u\in S:\hat F_a(u)\le q\}$, that threshold achieves an alien detection rate of at least $1-\eta$:
--
--   $$\mu_a\big((\hat\tau_q,\infty)\big)\ge1-\eta.$$
--
--   Equivalently, the event that Algorithm 1 returns a threshold whose alien detection rate is below $1-\eta$ has probability at most $\delta$. This is the paper's central result: a PAC guarantee on the fraction of aliens detected, for any anomaly detector, given the alien fraction $\alpha$.
--
--   **Formalization Note** The printed theorem also asserts that Algorithm 1 returns a threshold, i.e. that $\{u\in S:\hat F_a(u)\le q\}$ is nonempty. That claim is false: for $\alpha=0.9$, $q=0.001$, $\epsilon=0.9$, $\delta=0.05$ and $n=5$ (which exceeds the bound $\approx4.03$), with nominal scores uniform on $[0,1]$ and alien scores uniform on $[-1,0]$, the set is empty with probability at least $1-0.1^5$. The proof in Appendix A only shows that every $u$ with $\hat F_a(u)\le q$ has $F_a(u)\le q+\epsilon$, so the statement is the guarantee for the returned threshold whenever one is returned. The probability bound is stated as an upper bound $\delta$ on the failure event, and the independence of the two samples is built into their product law.
-- source:
--   Liu, Garrepalli, Dietterich, Fern and Hendrycks, Open Category Detection with PAC Guarantees, arXiv:1808.00529v1 (ICML 2018), Section 5, Theorem 1, p. 4; proof in Appendix A, p. 8

import Mathlib
import Definitions.Def_OpenCategoryPAC_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace OpenCategoryPAC

theorem theorem_1 (μ0 μa μm : Measure ℝ) [IsProbabilityMeasure μ0]
    [IsProbabilityMeasure μa] [IsProbabilityMeasure μm] (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hm : μm = mixture α μ0 μa) (hF0 : Continuous (cdf μ0)) (hFa : Continuous (cdf μa))
    (q ε δ : ℝ) (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1 - q) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (n : ℕ) (hn : sampleSizeBound α ε δ < n) :
    sampleLaw μ0 μm n
        {s | ∃ τ : ℝ, IsAlgThreshold α q s.1 s.2 τ ∧ detectionRate μa τ < 1 - (q + ε)} ≤
      ENNReal.ofReal δ := by sorry

end OpenCategoryPAC
