-- Prove2me | Theorems.Thm_OpenCategoryPAC_upper_bound_alien_cdf
-- name    : OpenCategoryPAC.upper_bound_alien_cdf
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T04:24:28.812854+00:00
-- url     : https://prove2.me/theorems/2f251439-be0f-4bee-99da-34d0b6b7422a
-- title:
--   Corollary 1, proof: $F'_a$ is a legal CDF and $F'_a\ge F_a$
-- statement:
--   Let $\mu_0,\mu_a$ be probability measures on $\mathbb R$ with CDFs $F_0,F_a$, let $0<\alpha\le\alpha'\le1$, and let $\mu_m=(1-\alpha)\mu_0+\alpha\mu_a$ with CDF $F_m$. Put
--
--   $$F'_a(x)=\frac{F_m(x)-(1-\alpha')F_0(x)}{\alpha'}.$$
--
--   Then:
--
--   1. $F'_a$ is a legal CDF: it is nondecreasing, $F'_a(-\infty)=0$, $F'_a(\infty)=1$, and it is the CDF of a probability measure on $\mathbb R$.
--   2. For all $x\in\mathbb R$, $\displaystyle F'_a(x)-F_a(x)=\frac{(\alpha-\alpha')(F_m(x)-F_0(x))}{\alpha\alpha'}$.
--   3. If the anomaly detector is admissible ($F_0\ge F_m$ on $\mathbb R$), then $F'_a(x)\ge F_a(x)$ for all $x\in\mathbb R$.
--
--   These are the facts the proof of Corollary 1 uses to reduce the case of an upper bound $\alpha'$ to Theorem 1.
--
--   **Formalization Note** The paper's $F'_a(-\infty)=0$ and $F'_a(\infty)=1$ are stated as limits at $\mp\infty$. "Legal CDF" is also stated as the existence of a probability measure with CDF $F'_a$, which is how the proof uses it. $\alpha'\le1$ is the paper's implicit reading of $\alpha'$ as an upper bound on a fraction.
-- source:
--   Liu, Garrepalli, Dietterich, Fern and Hendrycks, Open Category Detection with PAC Guarantees, arXiv:1808.00529v1 (ICML 2018), Appendix B (Proof for Corollary 1), p. 8

import Mathlib
import Definitions.Def_OpenCategoryPAC_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace OpenCategoryPAC

theorem upper_bound_alien_cdf (μ0 μa μm : Measure ℝ) [IsProbabilityMeasure μ0]
    [IsProbabilityMeasure μa] [IsProbabilityMeasure μm] (α α' : ℝ) (hα0 : 0 < α)
    (hαα' : α ≤ α') (hα'1 : α' ≤ 1) (hm : μm = mixture α μ0 μa) :
    (Monotone (alienCDF α' (cdf μm) (cdf μ0)) ∧
      Tendsto (alienCDF α' (cdf μm) (cdf μ0)) atBot (𝓝 0) ∧
      Tendsto (alienCDF α' (cdf μm) (cdf μ0)) atTop (𝓝 1) ∧
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ⇑(cdf ν) = alienCDF α' (cdf μm) (cdf μ0)) ∧
    (∀ t : ℝ, alienCDF α' (cdf μm) (cdf μ0) t - cdf μa t =
      (α - α') * (cdf μm t - cdf μ0 t) / (α * α')) ∧
    (IsAdmissible μ0 μm → ∀ t : ℝ, cdf μa t ≤ alienCDF α' (cdf μm) (cdf μ0) t) := by sorry

end OpenCategoryPAC
