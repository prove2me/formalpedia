-- Prove2me | Theorems.Thm_FreedmanTail_LowerTail_ineq_4_15
-- name    : FreedmanTail.LowerTail.ineq_4_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:16:00.991081+00:00
-- url     : https://prove2.me/theorems/3b11eb01-06d8-4e13-b5b6-050c34604e92
-- title:
--   (4.15) — φ(λ) ∫_0^∞ P{W < x} exp[−φ(λ)x] dx > exp[−λ(a + 1)]
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $W\ge0$ a random variable satisfying (4.11b): $E\{\exp[-f(\lambda)W]\}\ge\exp(-\lambda(a+1))$ for every $\lambda\ge0$, where $f(\lambda)=e^{-\lambda}-1+\lambda$. Let $\delta,a,b$ satisfy (4.12a)–(4.12c), and put $\lambda=(1+\delta)a/b$ and $\varphi(\lambda)=\lambda^2/2-\lambda^3/6$. Then
--
--   $$
--   \varphi(\lambda)\int_0^\infty P\{W<x\}\,e^{-\varphi(\lambda)x}\,dx>\exp[-\lambda(a+1)].
--   $$
--
--   The left side equals $E\{\exp[-\varphi(\lambda)W]\}$, and $0<\varphi<f$; this is the lower bound from which the proof of Proposition (4.10) subtracts the error terms $\eta_1,\dots,\eta_4$ to isolate the main term $\eta_5$.
--
--   **Formalization Note** The integral is over $[0,\infty)$ with respect to Lebesgue measure. Only (4.11b) and (4.12) are assumed.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 109 (PDF p. 10), display (4.15)

import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
import Definitions.Def_FreedmanTail_LowerTail_Hypotheses
import Definitions.Def_FreedmanTail_LowerTail_ProofNotation
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.15), p. 109: under (4.11b) and (4.12), with `λ = (1 + δ)a/b`
and `φ(λ) = λ²/2 − λ³/6`,
`φ(λ) ∫_0^∞ P{W < x} exp[−φ(λ)x] dx > exp[−λ(a + 1)]`. -/
theorem ineq_4_15 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    Real.exp (-(lamStar δ a b * (a + 1))) <
      phi (lamStar δ a b) *
        ∫ x in Set.Ici (0 : ℝ), P.real {ω | W ω < x} *
          Real.exp (-(phi (lamStar δ a b) * x)) := by sorry

end FreedmanTail.LowerTail
