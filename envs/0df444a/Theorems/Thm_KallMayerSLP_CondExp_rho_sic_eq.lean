-- Prove2me | Theorems.Thm_KallMayerSLP_CondExp_rho_sic_eq
-- name    : KallMayerSLP.CondExp.rho_sic_eq
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:10.23169+00:00
-- url     : https://prove2.me/theorems/786e7132-985a-4b4b-b316-7f5f30423b21
-- title:
--   §4.2, pp.158–159 — $\rho^-_{\mathrm{sic}}(\vartheta)=\rho_{\mathrm{cexp}}(\vartheta)\,\mathbb P(\vartheta<0)$
-- statement:
--   Let $\vartheta$ be an integrable random variable with distribution function $F_\vartheta$. Then
--   $$
--   \mathbb E[\vartheta^-]=-\int_{-\infty}^0 t\,dF_\vartheta(t),\qquad\rho^-_{\mathrm{sic}}(\vartheta)=\rho_{\mathrm{cexp}}(\vartheta)\,\mathbb P(\vartheta<0).
--   $$
--
--   This ties the conditional-expectation constraints of §4.2 to the integrated chance constraints of §4.1: the expected loss is the conditional expected loss times the probability of a loss.
--
--   Differences from the source:
--   - generalization: ϑ has a continuous distribution → ϑ integrable, no continuity assumption; reason: the identity does not use continuity, and every integrable ϑ with a continuous distribution is covered
--   - encoding: ∫_{-∞}^0 t dF_ϑ(t) → the integral of t over (-∞, 0] against the law of ϑ; reason: same integral; the point t = 0 contributes 0
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §4.2, pp.158–159

import Mathlib
import Definitions.Def_KallMayerSLP_CondExp_rhoCexp
import Definitions.Def_KallMayerSLP_CondExp_rhoSicMinus

open MeasureTheory

namespace KallMayerSLP.CondExp

/-- The relation `ρ⁻_sic(ϑ) = ρ_cexp(ϑ) ℙ(ϑ < 0)`, through
`𝔼[ϑ⁻] = -∫_{-∞}^0 t dF_ϑ(t) = 𝔼[-ϑ | ϑ < 0] · ℙ(ϑ < 0)`.
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §4.2, pp.158–159 (PDF 168–169).

**Formalization Note** The book assumes `ϑ` has a continuous distribution; the identity holds for
every integrable `ϑ`, with `∫_{-∞}^0 t dF_ϑ(t)` the integral over `(-∞, 0]` against the law of `ϑ`. -/
theorem rho_sic_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ϑ : Ω → ℝ) (hϑ : Measurable ϑ) (hint : Integrable ϑ μ) :
    rhoSicMinus μ ϑ = -∫ s in Set.Iic (0 : ℝ), s ∂(μ.map ϑ) ∧
      rhoSicMinus μ ϑ = rhoCexp μ ϑ * μ.real {ω | ϑ ω < 0} := by sorry

end KallMayerSLP.CondExp
