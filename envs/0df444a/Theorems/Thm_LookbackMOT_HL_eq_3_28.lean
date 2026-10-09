-- Prove2me | Theorems.Thm_LookbackMOT_HL_eq_3_28
-- name    : LookbackMOT.HL.eq_3_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:33:45.906991+00:00
-- url     : https://prove2.me/theorems/1f796986-d99f-43ea-a915-d9cbdb3c7683
-- title:
--   (3.28), p. 17 — for m ≥ X₀: inf_{ξ<m} φ(ξ, m) = inf_{ξ<m} c(ξ)/(m − ξ) = c(β(m))/(m − β(m))
-- statement:
--   Let $\mu$ be an integrable probability measure on $\mathbb R$ with mean $X_0$, $c(x)=\int(\xi-x)^+\mu(d\xi)$, and $\varphi$ as in (3.25). For every $m\ge X_0$,
--   $$\inf_{\xi<m}\varphi(\xi,m)=\inf_{\xi<m}\frac{c(\xi)}{m-\xi}.$$
--   Moreover, if $m<r^\mu$ (that is, $\mu((m,\infty))>0$) and either $m>X_0$ or $\ell^\mu>-\infty$ (the support of $\mu$ is bounded below), the function $\xi\mapsto c(\xi)/(m-\xi)$ on $(-\infty,m)$ has a largest minimizer $\beta(m)$ (Remark 3.1, (3.10)), and
--   $$\inf_{\xi<m}\frac{c(\xi)}{m-\xi}=\frac{c(\beta(m))}{m-\beta(m)} .$$
--
--   Above the spot, the pointwise minimization of the integrand of Lemma 3.2 is attained at Hobson's function $\beta$, the left-continuous inverse of the barycenter; its value is the tail $\mu^{HL}([m,\infty))$ of the Hardy–Littlewood transform.
--
--   **Formalization Note** The second equality is stated for $m<r^\mu$, i.e. $\mu((m,\infty))>0$, and, at $m=X_0$, for $\ell^\mu>-\infty$. For $m\ge r^\mu$ the page's $\beta(m)=m$ (3.11) makes $c(\beta(m))/(m-\beta(m))$ the undefined ratio $0/0$; at $m=X_0$ the page's $\beta(X_0)=\ell^\mu$ is $-\infty$ when the support of $\mu$ is unbounded below, and then no minimizer exists. Those two cases are left out. $\beta(m)$ is not given a closed form: the statement asserts that the set of minimizers has a greatest element and that the infimum is attained there.
-- source:
--   Galichon, Henry-Labordère & Touzi, A stochastic control approach to no-arbitrage bounds given marginals, with an application to lookback options, arXiv:1401.3921v1, p. 17, (3.28), with Remark 3.1 (3.10), p. 12

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting

open MeasureTheory ProbabilityTheory LookbackMOT.HL
open scoped NNReal ENNReal

namespace LookbackMOT.HL

theorem eq_3_28 (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (m : ℝ) (hm : X₀ ≤ m) :
    (⨅ ξ : Set.Iio m, phi μ X₀ ξ m) = (⨅ ξ : Set.Iio m, callPrice μ ξ / (m - ξ)) ∧
      ((X₀ < m ∨ ∃ a : ℝ, μ (Set.Iio a) = 0) → 0 < μ (Set.Ioi m) →
        ∃ β : ℝ, IsGreatest {ξ : ℝ | ξ < m ∧
            ∀ η : ℝ, η < m → callPrice μ ξ / (m - ξ) ≤ callPrice μ η / (m - η)} β ∧
          (⨅ ξ : Set.Iio m, callPrice μ ξ / (m - ξ)) = callPrice μ β / (m - β)) := by sorry

end LookbackMOT.HL
