-- Prove2me | Theorems.Thm_KallMayerSLP_CondExp_eq_4_27
-- name    : KallMayerSLP.CondExp.eq_4_27
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:24.411546+00:00
-- url     : https://prove2.me/theorems/3686cb95-e070-42c7-8210-7b1dc8b940b9
-- title:
--   Eq. (4.27), p.160 — $\mathbb E[\vartheta\mid\vartheta\ge\nu_\alpha]$ for an $\alpha$-quantile
-- statement:
--   Let $\vartheta$ be a random variable with finite expected value, $0<\alpha<1$ and $\nu_\alpha$ an $\alpha$-quantile of $\vartheta$. Then $\mathbb P(\vartheta\ge\nu_\alpha)>0$ and
--   $$
--   \mathbb E[\vartheta\mid\vartheta\ge\nu_\alpha]=\nu_\alpha+\frac{1}{\mathbb P(\vartheta\ge\nu_\alpha)}\,\mathbb E[(\vartheta-\nu_\alpha)^+].
--   $$
--
--   This holds for every distribution and is the bridge from the conditional tail mean to the objective of (4.30).
--
--   Differences from the source: none.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, eq. (4.27), pp.159–160

import Mathlib
import Definitions.Def_KallMayerSLP_CondExp_IsQuantile
import Definitions.Def_KallMayerSLP_CondExp_condTailMean

open MeasureTheory

namespace KallMayerSLP.CondExp

/-- For an `α`-quantile `ν`, `ℙ(ϑ ≥ ν) > 0` and
`𝔼[ϑ | ϑ ≥ ν] = ν + (1 / ℙ(ϑ ≥ ν)) 𝔼[(ϑ - ν)⁺]`.
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, eq. (4.27), pp.159–160 (PDF 169–170). -/
theorem eq_4_27 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ϑ : Ω → ℝ) (hϑ : Measurable ϑ) (hint : Integrable ϑ μ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (ν : ℝ) (hν : IsQuantile μ ϑ α ν) :
    0 < μ.real {ω | ν ≤ ϑ ω} ∧
      condTailMean μ ϑ ν = ν + 1 / μ.real {ω | ν ≤ ϑ ω} * ∫ ω, max (ϑ ω - ν) 0 ∂μ := by sorry

end KallMayerSLP.CondExp
