-- Prove2me | Theorems.Thm_OpenCategoryPAC_mixture_cdf_decomposition
-- name    : OpenCategoryPAC.mixture_cdf_decomposition
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:20:18.170031+00:00
-- url     : https://prove2.me/theorems/a437101b-5f70-4c4e-85cf-061010d718b2
-- title:
--   Section 4: the mixture CDF and the recovered alien CDF
-- statement:
--   Let $\mu_0$ and $\mu_a$ be probability measures on $\mathbb R$ (the nominal and alien score laws) with CDFs $F_0$ and $F_a$, and let $0<\alpha\le1$. Then the mixture $\mu_m=(1-\alpha)\mu_0+\alpha\mu_a$ is a probability measure whose CDF $F_m$ satisfies, for all $t\in\mathbb R$,
--
--   $$F_m(t)=(1-\alpha)F_0(t)+\alpha F_a(t),\qquad F_a(t)=\frac{F_m(t)-(1-\alpha)F_0(t)}{\alpha}.$$
--
--   This identity is the basis of the estimate $\hat F_a$ of eq. (1).
-- source:
--   Liu, Garrepalli, Dietterich, Fern and Hendrycks, Open Category Detection with PAC Guarantees, arXiv:1808.00529v1 (ICML 2018), Section 4, unnumbered displays before eq. (1), p. 3

import Mathlib
import Definitions.Def_OpenCategoryPAC_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace OpenCategoryPAC

theorem mixture_cdf_decomposition (μ0 μa : Measure ℝ) [IsProbabilityMeasure μ0]
    [IsProbabilityMeasure μa] (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    IsProbabilityMeasure (mixture α μ0 μa) ∧
    (∀ t : ℝ, cdf (mixture α μ0 μa) t = (1 - α) * cdf μ0 t + α * cdf μa t) ∧
    (∀ t : ℝ, cdf μa t = alienCDF α (cdf (mixture α μ0 μa)) (cdf μ0) t) := by sorry

end OpenCategoryPAC
