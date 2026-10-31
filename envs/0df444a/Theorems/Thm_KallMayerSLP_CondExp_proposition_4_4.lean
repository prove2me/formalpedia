-- Prove2me | Theorems.Thm_KallMayerSLP_CondExp_proposition_4_4
-- name    : KallMayerSLP.CondExp.proposition_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:10:36.111574+00:00
-- url     : https://prove2.me/theorems/1df3659d-5aca-4a6e-ac07-6e9b26c3d372
-- title:
--   Proposition 4.4 — a log-concave density has decreasing mean residual life
-- statement:
--   Let $\xi$ be a random variable with a continuous distribution given by a log-concave density $f$ on $\mathbb R$, and assume that the expected value of $\xi$ exists. Then the **mean residual life**
--   $$
--   l(t)=\mathbb E[\xi-t\mid\xi-t>0]=\frac{\int_{\{\xi>t\}}(\xi-t)\,d\mu}{\mathbb P(\xi>t)}
--   $$
--   is a monotonically decreasing function of $t$ on $\{t\mid\mathbb P(\xi>t)>0\}$: for $s\le t$ in that set, $l(s)\ge l(t)$.
--
--   The result is what makes the conditional-expectation constraint (4.26) a linear constraint when only the right-hand side is random.
--
--   **Formalization Note** $l$ is the published function `StochasticOrders.MeanResidualLife.mrl`; its value outside $\{t\mid\mathbb P(\xi>t)>0\}$ plays no part here. The density may vanish outside an interval, and no continuity of $f$ is assumed. Finiteness of the mean is the book's hypothesis and is kept, although a log-concave density has one anyway.
--
--   Differences from the source:
--   - reading: l is a monotonically decreasing function of t, with no domain stated → AntitoneOn l on {t | ℙ(ξ > t) > 0}, in the weak sense; reason: l is an elementary conditional expectation defined only there, and strict decrease is false: the exponential law has constant l
--   - encoding: continuous distribution with a logconcave density function → μ.map ξ = volume.withDensity f with f log-concave on ℝ (Definition 1.3 with C = ℝ); reason: a density makes the distribution continuous, so no separate continuity hypothesis is needed
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Proposition 4.4, p.159

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_mrl
import Definitions.Def_LogConcaveOn

open MeasureTheory

namespace KallMayerSLP.CondExp

open StochasticOrders.MeanResidualLife

/-- If `ξ` has a continuous distribution with a log-concave density and `𝔼ξ` exists, then the mean
residual life `l(t) := 𝔼[ξ - t | ξ - t > 0]` is a monotonically decreasing function of `t`.
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Proposition 4.4, p.159 (PDF 169).

**Formalization Note** `l` is an elementary conditional expectation, defined by the book only where
`ℙ(ξ > t) > 0`, so "monotonically decreasing" is antitonicity on `{t | ℙ(ξ > t) > 0}`; the `0` of the
platform's `mrl` outside that set plays no part. Decreasing is weak: the exponential law has constant
`l`. The density is `f`, log-concave on `ℝ` in the sense of Definition 1.3 (it may vanish outside an
interval), `μ.map ξ = volume.withDensity f`. No continuity of `f` is assumed. -/
theorem proposition_4_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → ℝ) (hξ : Measurable ξ) (f : ℝ → ℝ)
    (hdens : μ.map ξ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (hlog : ConvexOptimization.LogConcaveOn Set.univ f) (hint : Integrable ξ μ) :
    AntitoneOn (mrl μ ξ) {t | 0 < μ {ω | t < ξ ω}} := by sorry

end KallMayerSLP.CondExp
