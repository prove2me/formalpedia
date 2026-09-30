-- Prove2me | Theorems.Thm_MixFlex_RiskNeutral_expectedShortfall_affine
-- name    : MixFlex.RiskNeutral.expectedShortfall_affine
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:58:18.62949+00:00
-- url     : https://prove2.me/theorems/103d5577-bfea-45a5-ad31-d81641f1f889
-- title:
--   AT02 Prop. 3.1(iii)–(iv): $ES_\alpha(aX+b)=aES_\alpha(X)-b$, as used in the proof of PROPOSITION 1(iii)
-- statement:
--   Let $Z$ be an integrable random variable on a probability space, $a>0$, $b\in\mathbb R$ and $\alpha\in(0,1)$. Then the Acerbi–Tasche $\alpha$-expected shortfall satisfies
--   $$
--   ES_\alpha(aZ+b)=a\,ES_\alpha(Z)-b.
--   $$
--   This combines positive homogeneity and translation invariance of expected shortfall (Acerbi and Tasche 2002, Proposition 3.1(iii) and (iv)); the proof of Proposition 1(iii) uses it to show that expected shortfall is additive on perfectly positively correlated demands.
-- source:
--   Acerbi and Tasche (2002), Proposition 3.1(iii)–(iv), as quoted in Tomlin and Wang, On the value of mix flexibility and dual sourcing in unreliable newsvendor networks, Manufacturing Service Oper. Management 7(1), 2005, p. 52, Appendix A, proof of PROPOSITION 1(iii)

import Mathlib
import Definitions.Def_MixFlex_RiskNeutral_Model

namespace MixFlex.RiskNeutral

open MeasureTheory ProbabilityTheory

/-- Positive homogeneity and translation invariance of expected shortfall (Acerbi–Tasche 2002,
Proposition 3.1(iii)–(iv)), as quoted in the proof of Proposition 1(iii), p. 52:
`ES_α(aZ + b) = a ES_α(Z) − b` for `a > 0`. -/
theorem expectedShortfall_affine {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hmeas : Measurable Z) (hint : Integrable Z μ)
    (a b : ℝ) (ha : 0 < a) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    expectedShortfall μ (fun ω => a * Z ω + b) α = a * expectedShortfall μ Z α - b := by sorry

end MixFlex.RiskNeutral
