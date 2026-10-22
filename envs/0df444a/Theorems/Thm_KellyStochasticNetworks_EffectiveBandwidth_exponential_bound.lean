-- Prove2me | Theorems.Thm_KellyStochasticNetworks_EffectiveBandwidth_exponential_bound
-- name    : KellyStochasticNetworks.EffectiveBandwidth.exponential_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:48:12.825433+00:00
-- url     : https://prove2.me/theorems/64edea1a-87e1-4827-9945-9c31f624dc65
-- title:
--   Equation (6.1) — exponential probability bound
-- statement:
--   Let $Y$ be a measurable real random variable on a probability space $(\Omega,\mathcal F,P)$, and let $s\ge0$. Then
--   $$P(Y>0)=\mathbb E[\mathbf1_{\{Y>0\}}]\le\mathbb E[e^{sY}].$$
--   The exponential expectation may be infinite. This is the exponential upper bound that precedes optimization over the tilt and the large-deviation limits.
--
--   **Formalization Note** Both expectations in the statement are nonnegative Lebesgue integrals in $[0,+\infty]$. There is no exponential-integrability assumption. The referenced proved Chernoff theorem supplies the finite-expectation, closed-tail core; this item retains the source's strict event and infinite-expectation case.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 135 (PDF p. 143), Eq. (6.1); DOI https://doi.org/10.1017/CBO9781139565363

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace KellyStochasticNetworks.EffectiveBandwidth

theorem exponential_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (s : ℝ) (hs : 0 ≤ s) :
    P {ω | 0 < Y ω} =
      (∫⁻ ω, Set.indicator {ω | 0 < Y ω} (fun _ => (1 : ℝ≥0∞)) ω ∂P) ∧
    P {ω | 0 < Y ω} ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (s * Y ω)) ∂P := by sorry

end KellyStochasticNetworks.EffectiveBandwidth
