-- Prove2me | Theorems.Thm_KallMayerSLP_CondExp_eq_4_33
-- name    : KallMayerSLP.CondExp.eq_4_33
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:00.741074+00:00
-- url     : https://prove2.me/theorems/7b4f1455-4e75-4932-b199-ee158c8aba07
-- title:
--   Eq. (4.33), p.161 — CVaR is a conditional expectation for continuous $F_\vartheta$
-- statement:
--   Let $\vartheta$ have finite expected value and a continuous distribution function, and let $0<\alpha<1$. Then
--   $$
--   \nu_c(\vartheta,\alpha)=\mathbb E[\vartheta\mid\vartheta\ge\nu(\vartheta,\alpha)].
--   $$
--
--   This is the interpretation of CVaR as the expected loss given that the loss reaches VaR.
--
--   Differences from the source: none.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, eq. (4.33), p.161

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_KallMayerSLP_CondExp_condTailMean
import Definitions.Def_KallMayerSLP_CondExp_cvar

open MeasureTheory

namespace KallMayerSLP.CondExp

/-- For continuous `F_ϑ`, `ν_c(ϑ, α) = 𝔼[ϑ | ϑ ≥ ν(ϑ, α)]`.
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, eq. (4.33), p.161 (PDF 171). -/
theorem eq_4_33 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ϑ : Ω → ℝ) (hϑ : Measurable ϑ) (hint : Integrable ϑ μ)
    (hF : Continuous fun z : ℝ => μ.real {ω | ϑ ω ≤ z}) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    cvar μ ϑ α = condTailMean μ ϑ (MultistageStochastic.valueAtRisk μ ϑ α) := by sorry

end KallMayerSLP.CondExp
