-- Prove2me | Theorems.Thm_KallMayerSLP_CondExp_quantile_set_eq_Icc
-- name    : KallMayerSLP.CondExp.quantile_set_eq_Icc
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:18.871606+00:00
-- url     : https://prove2.me/theorems/e8ee2bab-9ff9-4da1-92cd-dac8d498aa8a
-- title:
--   §3, p.144 — the $\alpha$-quantiles form a closed interval with left endpoint $\nu(\vartheta,\alpha)$
-- statement:
--   Let $\vartheta$ be a random variable with distribution function $F_\vartheta$ and $0<\alpha<1$, and let $\nu(\vartheta,\alpha)=\min\{z\mid F_\vartheta(z)\ge\alpha\}$. Then this minimum is attained, and the set of $\alpha$-quantiles of $\vartheta$ is the nonempty closed interval
--   $$
--   \{z\mid z\text{ is an }\alpha\text{-quantile of }\vartheta\}=\big[\nu(\vartheta,\alpha),\ \inf\{z\mid F_\vartheta(z)>\alpha\}\big].
--   $$
--
--   Together with the published theorem `RUCVaR.MinFormula.theorem_10`, whose argmin is this interval for $\vartheta=\zeta(x,\xi)$, this gives Proposition 4.5 in the book's quantile form.
--
--   **Formalization Note** $\nu(\vartheta,\alpha)$ is the published `MultistageStochastic.valueAtRisk`, an infimum; the first clause of the theorem is that it is a minimum.
--
--   Differences from the source:
--   - encoding: a non-empty closed interval, with ν(ϑ, α) its left endpoint → Icc ν b with ν ≤ b and b := inf{z | F(z) > α}; reason: the right endpoint is named explicitly, which is what links it to the upper VaR of the reference
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §3, eq. (3.1) and the surrounding text, p.144

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_KallMayerSLP_CondExp_IsQuantile

open MeasureTheory

namespace KallMayerSLP.CondExp

/-- For `0 < α < 1` the set of `α`-quantiles is a nonempty closed interval, and
`ν(ϑ, α) := min {z | F_ϑ(z) ≥ α}` is its left endpoint.
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §3, eq. (3.1) and the surrounding text,
p.144 (PDF 154).

**Formalization Note** `ν(ϑ, α)` is the published `MultistageStochastic.valueAtRisk`, an `inf`; the
first clause says the book's `min` is attained. The right endpoint is written `inf {z | F_ϑ(z) > α}`.
With `Ω = Fin m → ℝ` and `ϑ = f x`, the interval is exactly `[VaR, VaR⁺]` of
`RUCVaR.MinFormula.theorem_10`, which turns that reference into the quantile form of Proposition 4.5. -/
theorem quantile_set_eq_Icc {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ϑ : Ω → ℝ) (hϑ : Measurable ϑ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    IsLeast {z : ℝ | α ≤ μ.real {ω | ϑ ω ≤ z}} (MultistageStochastic.valueAtRisk μ ϑ α) ∧
      MultistageStochastic.valueAtRisk μ ϑ α ≤ sInf {z : ℝ | α < μ.real {ω | ϑ ω ≤ z}} ∧
      {z : ℝ | IsQuantile μ ϑ α z} =
        Set.Icc (MultistageStochastic.valueAtRisk μ ϑ α)
          (sInf {z : ℝ | α < μ.real {ω | ϑ ω ≤ z}}) := by sorry

end KallMayerSLP.CondExp
