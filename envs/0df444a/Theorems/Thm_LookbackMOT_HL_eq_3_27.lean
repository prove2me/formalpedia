-- Prove2me | Theorems.Thm_LookbackMOT_HL_eq_3_27
-- name    : LookbackMOT.HL.eq_3_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:33:53.840353+00:00
-- url     : https://prove2.me/theorems/0f48b26c-393f-4d84-8a8b-f1455493d2f6
-- title:
--   (3.27), p. 17 — for μ on [0, ∞) and m < X₀: inf_{ξ<m} φ(ξ, m) = φ(0, m) = 0
-- statement:
--   Let $\mu$ be a probability measure on $[0,\infty)$ with finite mean $X_0=\int x\,\mu(dx)$, and let $\varphi(x,m)=\big(c(x)-c_0(x)\mathbf 1_{m<X_0}\big)/(m-x)$ with $c(x)=\int(\xi-x)^+\mu(d\xi)$ and $c_0(x)=(X_0-x)^+$. Then for every $m<X_0$,
--   $$\inf_{\xi<m}\varphi(\xi,m)=\varphi(0,m)=0 .$$
--
--   Below the spot, the pointwise minimization of the integrand of Lemma 3.2 gives $0$: the free boundary can be pushed down to the lower end of the support and contributes nothing to the upper bound.
--
--   **Formalization Note** The hypothesis $\mu([0,\infty))=1$ is Remark 2.2's (the page uses "$c(x)\ge c_0(x)$ for all $x\ge0$" and the point $0$). For $m\le0$ the point $0$ is not in $\{\xi<m\}$, but $\varphi(0,m)=0$ still holds (for $m=0$ through the Lean convention $a/0=0$, where both $c(0)-c_0(0)=0$), and the statement is kept for all $m<X_0$ as printed. The infimum is a real infimum over $\{\xi<m\}$, a nonempty set on which $\varphi(\cdot,m)\ge0$.
-- source:
--   Galichon, Henry-Labordère & Touzi, A stochastic control approach to no-arbitrage bounds given marginals, with an application to lookback options, arXiv:1401.3921v1, p. 17, (3.27), step (1) of the proof of Lemma 3.3

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting

open MeasureTheory ProbabilityTheory LookbackMOT.HL
open scoped NNReal ENNReal

namespace LookbackMOT.HL

theorem eq_3_27 (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (hμpos : μ (Set.Ici 0) = 1) (m : ℝ) (hm : m < X₀) :
    (⨅ ξ : Set.Iio m, phi μ X₀ ξ m) = 0 ∧ phi μ X₀ 0 m = 0 := by sorry

end LookbackMOT.HL
