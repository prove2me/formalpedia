-- Prove2me | Theorems.Thm_FreedmanTail_LowerTail_ineq_4_19
-- name    : FreedmanTail.LowerTail.ineq_4_19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:14:04.56577+00:00
-- url     : https://prove2.me/theorems/f818e69b-eab5-4dcb-93cd-63a06fe6fe7e
-- title:
--   (4.19), corrected — P{W < x} < (1/8 − 1/50) exp[−(1 + δ)k] for 0 ≤ x ≤ Na
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $W\ge0$ a random variable satisfying (4.11a)–(4.11b) for every $\lambda\ge0$, and let $\delta,a,b$ satisfy (4.12a)–(4.12c). Put $k=a^2/b$ and $N=2/\delta^2$. Then for every $x$ with $0\le x\le Na$,
--
--   $$
--   P\{W<x\}<\theta=\left(\frac18-\frac1{50}\right)\exp[-(1+\delta)k].
--   $$
--
--   This is the pointwise bound on the first interval $I_1=[0,Na]$ that gives (4.16:1).
--
--   **Formalization Note** The page prints $\theta=(\tfrac18-\tfrac1{50})\exp[-(1+\delta)]$, without the factor $k$ in the exponent. That printed bound is true but too weak for its use: the next display, $\eta_1<\theta$, must give (4.16:1), $\eta_1<(\tfrac18-\tfrac1{50})\exp[-(1+\delta)k]$, and the page's own argument ($a^2/(a+x)>3k>(1+\delta+\tfrac16)k$ and $\exp(-k/6)<2^{-5}<\tfrac18-\tfrac1{50}$) proves the form with $k$. The corrected form is stated. The statement assumes the full hypotheses of Proposition (4.10).
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 110 (PDF p. 11), display (4.19) (misprinted exponent corrected)

import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
import Definitions.Def_FreedmanTail_LowerTail_Hypotheses
import Definitions.Def_FreedmanTail_LowerTail_ProofNotation
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.19), p. 110, corrected: under (4.11), (4.12), if `0 ≤ x ≤ Na` then
`P{W < x} < θ = (1/8 − 1/50) exp[−(1 + δ)k]`. The page prints `exp[−(1 + δ)]`, without the
factor `k = a²/b`; the proof on the page, and its use in (4.16:1), give the form with `k`. -/
theorem ineq_4_19
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    ∀ x : ℝ, 0 ≤ x → x ≤ NStar δ * a →
      P.real {ω | W ω < x} < (1 / 8 - 1 / 50) * Real.exp (-((1 + δ) * kStar a b)) := by sorry

end FreedmanTail.LowerTail
