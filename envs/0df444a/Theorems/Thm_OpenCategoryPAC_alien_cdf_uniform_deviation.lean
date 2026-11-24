-- Prove2me | Theorems.Thm_OpenCategoryPAC_alien_cdf_uniform_deviation
-- name    : OpenCategoryPAC.alien_cdf_uniform_deviation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:22:19.243454+00:00
-- url     : https://prove2.me/theorems/8070b481-cc96-401d-8a72-c9e604513b8e
-- title:
--   Theorem 1, proof: $P(\sup_x|\hat F_a(x)-F_a(x)|>\epsilon)\le\delta$
-- statement:
--   Let $\mu_0,\mu_a$ be probability measures on $\mathbb R$ with continuous CDFs $F_0,F_a$, let $0<\alpha\le1$, and let $\mu_m=(1-\alpha)\mu_0+\alpha\mu_a$ with CDF $F_m$. Let $S_0$ consist of $n$ i.i.d. draws from $\mu_0$ and, independently, $S_m$ of $n$ i.i.d. draws from $\mu_m$, and let $\hat F_a$ be the estimate of eq. (1). For $\epsilon>0$ and $\delta\in(0,1)$, if
--
--   $$n>\frac12\ln\frac{2}{1-\sqrt{1-\delta}}\left(\frac1\epsilon\right)^2\left(\frac{2-\alpha}{\alpha}\right)^2,$$
--
--   then
--
--   $$P\Big(\sup_x|\hat F_a(x)-F_a(x)|>\epsilon\Big)\le\delta.$$
--
--   This is the uniform deviation bound established in the proof of Theorem 1 from Massart's form of the Dvoretzky–Kiefer–Wolfowitz inequality (eq. (2)) applied to each sample.
--
--   **Formalization Note** The probability is that of the product law of the two samples, which encodes the independence of $S_0$ and $S_m$ used in the last step of the proof. The bound is stated for the measure of the deviation event itself (an outer measure if the event were not measurable). The paper writes the proof for $\epsilon\in(0,1-q)$, but $q$ does not enter this bound, so only $\epsilon>0$ is assumed.
-- source:
--   Liu, Garrepalli, Dietterich, Fern and Hendrycks, Open Category Detection with PAC Guarantees, arXiv:1808.00529v1 (ICML 2018), Appendix A (Proof for Theorem 1), p. 8, using eq. (2)

import Mathlib
import Definitions.Def_OpenCategoryPAC_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace OpenCategoryPAC

theorem alien_cdf_uniform_deviation (μ0 μa μm : Measure ℝ) [IsProbabilityMeasure μ0]
    [IsProbabilityMeasure μa] [IsProbabilityMeasure μm] (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hm : μm = mixture α μ0 μa) (hF0 : Continuous (cdf μ0)) (hFa : Continuous (cdf μa))
    (ε δ : ℝ) (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1) (n : ℕ)
    (hn : sampleSizeBound α ε δ < n) :
    sampleLaw μ0 μm n {s | ε < supDev (alienCDFEst α s.1 s.2) (cdf μa)} ≤ ENNReal.ofReal δ := by sorry

end OpenCategoryPAC
