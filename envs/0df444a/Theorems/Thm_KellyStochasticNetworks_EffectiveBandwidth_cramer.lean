-- Prove2me | Theorems.Thm_KellyStochasticNetworks_EffectiveBandwidth_cramer
-- name    : KellyStochasticNetworks.EffectiveBandwidth.cramer
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:48:11.803214+00:00
-- url     : https://prove2.me/theorems/7c13464f-2d95-4a4a-bc70-8d54373ec204
-- title:
--   Theorem 6.2 — Cramér’s theorem with a local MGF
-- statement:
--   Let $X_1,X_2,\ldots$ be independent identically distributed measurable real random variables on a probability space with law $P$. Put $M(s)=\log\mathbb E[e^{sX_1}]$. Assume that $M$ is finite in an open neighborhood of zero, that $\mathbb E X_1<c$, and that $P(X_1>c)>0$. Assume also that the infimum of $M(s)-cs$ over $s\ge0$ is attained at a point $s_*$ in the interior of the interval where $M$ is finite. Then
--   $$\lim_{n\to\infty}\frac1n\log P\left(\sum_{i=1}^nX_i>nc\right)=\inf_{s\ge0}\{M(s)-cs\}.$$
--   This is the exact fixed-time logarithmic asymptotic used by the chapter. Local finiteness, rather than finiteness for every real tilt, is part of the statement.
--
--   **Formalization Note** The first variable is `X 0`; the scale is $n=N+1$, excluding division by zero without changing the limit. Local finiteness is expressed by integrability of the exponential in an open interval, both at zero and at $s_*$. The minimizer is specified by its inequality against every nonnegative tilt. All logarithms and the infimum are extended-real; the expectation in the mean assumption is legitimate because the local MGF condition implies integrability. No density assumption is imposed, in accordance with Remark 6.3.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed pp. 135–136 (PDF pp. 143–144), Theorem 6.2 and its standing assumptions; DOI https://doi.org/10.1017/CBO9781139565363

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

namespace KellyStochasticNetworks.EffectiveBandwidth

theorem cramer {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (c : ℝ) (hmean : ∫ ω, X 0 ω ∂P < c)
    (htail : 0 < P {ω | c < X 0 ω})
    (hlocal : ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ →
      Integrable (fun ω => Real.exp (s * X 0 ω)) P) :
    let M : ℝ → EReal := fun s =>
      ENNReal.log (∫⁻ ω, ENNReal.ofReal (Real.exp (s * X 0 ω)) ∂P)
    (∃ sStar : ℝ, 0 ≤ sStar ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s - sStar| < δ →
        Integrable (fun ω => Real.exp (s * X 0 ω)) P) ∧
      (∀ s : ℝ, 0 ≤ s → M sStar - ((c * sStar : ℝ) : EReal) ≤
        M s - ((c * s : ℝ) : EReal))) →
    Tendsto
      (fun N : ℕ => ((((N + 1 : ℕ) : ℝ)⁻¹ : EReal) *
        ENNReal.log (P {ω | ((N + 1 : ℕ) : ℝ) * c <
          ∑ i ∈ Finset.range (N + 1), X i ω})))
      atTop (𝓝 (⨅ s : {s : ℝ // 0 ≤ s}, M s.val - ((c * s.val : ℝ) : EReal))) := by sorry

end KellyStochasticNetworks.EffectiveBandwidth
