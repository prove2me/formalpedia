-- Prove2me | Theorems.Thm_OpenCategoryPAC_corollary_1
-- name    : OpenCategoryPAC.corollary_1
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:25:54.504665+00:00
-- url     : https://prove2.me/theorems/d6d602fc-7845-4ff0-9693-ab8f2a81d268
-- title:
--   Corollary 1 (as proved): the guarantee with an upper bound $\alpha'\ge\alpha$
-- statement:
--   Assume the setting of Theorem 1: score laws $\mu_0,\mu_a$ with continuous CDFs, $0<\alpha\le1$, $\mu_m=(1-\alpha)\mu_0+\alpha\mu_a$, and independent samples $S_0\sim\mu_0^{\otimes n}$, $S_m\sim\mu_m^{\otimes n}$. Assume also that the anomaly detector is admissible, $F_0(x)\ge F_m(x)$ for all $x\in\mathbb R$. Let $\alpha'$ be an upper bound on the true fraction, $\alpha\le\alpha'\le1$, and run Algorithm 1 with $\alpha'$ in place of $\alpha$. Let $q>0$, $\epsilon\in(0,1-q)$, $\delta\in(0,1)$, and suppose
--
--   $$n>\frac12\ln\frac{2}{1-\sqrt{1-\delta}}\left(\frac1\epsilon\right)^2\left(\frac{2-\alpha'}{\alpha'}\right)^2.$$
--
--   Then, with probability at least $1-\delta$, if Algorithm 1 returns a threshold $\hat\tau'_q$, that threshold achieves an alien detection rate of at least $1-\eta$, $\eta=q+\epsilon$:
--
--   $$\mu_a\big((\hat\tau'_q,\infty)\big)\ge1-\eta.$$
--
--   So knowing an upper bound on the alien fraction suffices, at the price of a more conservative threshold.
--
--   **Formalization Note** As in Theorem 1, the printed claim that Algorithm 1 returns a threshold is not proved and is false in general. The statement gives the guarantee for the returned threshold whenever one is returned, as an upper bound $\delta$ on the probability of the failure event. $\alpha'\le1$ is the paper's implicit reading of $\alpha'$ as an upper bound on a fraction.
-- source:
--   Liu, Garrepalli, Dietterich, Fern and Hendrycks, Open Category Detection with PAC Guarantees, arXiv:1808.00529v1 (ICML 2018), Section 5, Corollary 1, p. 4; proof in Appendix B, p. 8

import Mathlib
import Definitions.Def_OpenCategoryPAC_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace OpenCategoryPAC

theorem corollary_1 (μ0 μa μm : Measure ℝ) [IsProbabilityMeasure μ0]
    [IsProbabilityMeasure μa] [IsProbabilityMeasure μm] (α α' : ℝ) (hα0 : 0 < α)
    (hαα' : α ≤ α') (hα'1 : α' ≤ 1)
    (hm : μm = mixture α μ0 μa) (hF0 : Continuous (cdf μ0)) (hFa : Continuous (cdf μa))
    (hadm : IsAdmissible μ0 μm)
    (q ε δ : ℝ) (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1 - q) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (n : ℕ) (hn : sampleSizeBound α' ε δ < n) :
    sampleLaw μ0 μm n
        {s | ∃ τ : ℝ, IsAlgThreshold α' q s.1 s.2 τ ∧ detectionRate μa τ < 1 - (q + ε)} ≤
      ENNReal.ofReal δ := by sorry

end OpenCategoryPAC
