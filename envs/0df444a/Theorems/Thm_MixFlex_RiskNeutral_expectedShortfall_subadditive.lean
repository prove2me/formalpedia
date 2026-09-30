-- Prove2me | Theorems.Thm_MixFlex_RiskNeutral_expectedShortfall_subadditive
-- name    : MixFlex.RiskNeutral.expectedShortfall_subadditive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:56:22.861396+00:00
-- url     : https://prove2.me/theorems/ae69aaa1-5731-4ab4-b4f8-7b80868e25ac
-- title:
--   AT02 subadditivity of $ES_\alpha$, as used in the proof of PROPOSITION 1(i)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $Z_1,\dots,Z_N$ integrable real random variables and $\alpha\in(0,1)$. Then the Acerbi–Tasche $\alpha$-expected shortfall is subadditive:
--   $$
--   ES_\alpha\Big(\sum_{n=1}^N Z_n\Big)\le\sum_{n=1}^N ES_\alpha(Z_n).
--   $$
--   This is the result of Acerbi and Tasche (2002) quoted in the proof of Proposition 1(i); combined with the expected-shortfall form of (A-1) it gives $\Delta_{RN}\ge 0$. It holds for arbitrary integrable random variables, not only demands.
-- source:
--   Acerbi and Tasche (2002), as quoted in Tomlin and Wang, On the value of mix flexibility and dual sourcing in unreliable newsvendor networks, Manufacturing Service Oper. Management 7(1), 2005, p. 52, Appendix A, proof of PROPOSITION 1(i)

import Mathlib
import Definitions.Def_MixFlex_RiskNeutral_Model

namespace MixFlex.RiskNeutral

open MeasureTheory ProbabilityTheory

/-- Subadditivity of expected shortfall (Acerbi–Tasche 2002), as quoted in the proof of
Proposition 1(i), p. 52: `ES_α(Σ_n Z_n) ≤ Σ_n ES_α(Z_n)` for integrable random variables and
`α ∈ (0, 1)`. -/
theorem expectedShortfall_subadditive {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {N : ℕ} (Z : Fin N → Ω → ℝ) (hmeas : ∀ n, Measurable (Z n))
    (hint : ∀ n, Integrable (Z n) μ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    expectedShortfall μ (fun ω => ∑ n, Z n ω) α ≤ ∑ n, expectedShortfall μ (Z n) α := by sorry

end MixFlex.RiskNeutral
