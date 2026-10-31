-- Prove2me | Theorems.Thm_KallMayerSLP_CondExp_eq_4_28
-- name    : KallMayerSLP.CondExp.eq_4_28
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:14.965982+00:00
-- url     : https://prove2.me/theorems/55270111-5e73-41cf-874b-4f1bc5ca0079
-- title:
--   Eq. (4.28), p.160 — the conditional tail mean for continuous $F_\vartheta$
-- statement:
--   Let $\vartheta$ have finite expected value and a continuous distribution function $F_\vartheta$, let $0<\alpha<1$ and let $\nu_\alpha$ be an $\alpha$-quantile. Then $F_\vartheta(\nu_\alpha)=\alpha$, $\mathbb P(\vartheta\ge\nu_\alpha)=1-\alpha$, and
--   $$
--   \mathbb E[\vartheta\mid\vartheta\ge\nu_\alpha]=\nu_\alpha+\frac{1}{1-\alpha}\,\mathbb E[(\vartheta-\nu_\alpha)^+].
--   $$
--
--   The right side is the objective $u_c$ at $\nu_\alpha$, which is why CVaR is a conditional expectation in the continuous case.
--
--   Differences from the source: none.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, eq. (4.28), p.160

import Mathlib
import Definitions.Def_KallMayerSLP_CondExp_IsQuantile
import Definitions.Def_KallMayerSLP_CondExp_condTailMean

open MeasureTheory

namespace KallMayerSLP.CondExp

/-- If `F_ϑ` is continuous and `ν` is an `α`-quantile, then `F_ϑ(ν) = α`, `ℙ(ϑ ≥ ν) = 1 - α` and
`𝔼[ϑ | ϑ ≥ ν] = ν + (1 / (1 - α)) 𝔼[(ϑ - ν)⁺]`.
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, eq. (4.28), p.160 (PDF 170). -/
theorem eq_4_28 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ϑ : Ω → ℝ) (hϑ : Measurable ϑ) (hint : Integrable ϑ μ)
    (hF : Continuous fun z : ℝ => μ.real {ω | ϑ ω ≤ z}) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (ν : ℝ) (hν : IsQuantile μ ϑ α ν) :
    μ.real {ω | ϑ ω ≤ ν} = α ∧ μ.real {ω | ν ≤ ϑ ω} = 1 - α ∧
      condTailMean μ ϑ ν = ν + 1 / (1 - α) * ∫ ω, max (ϑ ω - ν) 0 ∂μ := by sorry

end KallMayerSLP.CondExp
