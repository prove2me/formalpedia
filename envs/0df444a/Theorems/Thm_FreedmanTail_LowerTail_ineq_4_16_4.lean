-- Prove2me | Theorems.Thm_FreedmanTail_LowerTail_ineq_4_16_4
-- name    : FreedmanTail.LowerTail.ineq_4_16_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:21:13.928293+00:00
-- url     : https://prove2.me/theorems/5a76b947-0a24-493f-ae6d-36fb564f4233
-- title:
--   (4.16:i), i = 4 — η_4 < (1/8) exp[−(1 + δ)k]
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $W\ge0$ a measurable random variable satisfying (4.11a)–(4.11b) for every $\lambda\ge0$, and let $\delta,a,b$ satisfy (4.12a)–(4.12c). With $\lambda=(1+\delta)a/b$, $\varphi(\lambda)=\lambda^2/2-\lambda^3/6$, $k=a^2/b$ and $I_4=(2b,\infty)$, let $\eta_4=\varphi(\lambda)\int_{I_4}P\{W<x\}e^{-\varphi(\lambda)x}\,dx$. Then
--
--   $$
--   \eta_4<\frac18\exp[-(1+\delta)k].
--   $$
--
--   This bounds the fourth (tail) error term of the proof of Proposition (4.10).
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 110 (PDF p. 11), display (4.16:i), i = 4; proof p. 112

import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
import Definitions.Def_FreedmanTail_LowerTail_Hypotheses
import Definitions.Def_FreedmanTail_LowerTail_ProofNotation
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.16:i) for `i = 4`, p. 110: `η₄ < (1/8) exp[−(1 + δ)k]`. -/
theorem ineq_4_16_4
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    eta P W δ a b (I4 b) < 1 / 8 * Real.exp (-((1 + δ) * kStar a b)) := by sorry

end FreedmanTail.LowerTail
