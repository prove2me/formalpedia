-- Prove2me | Theorems.Thm_FreedmanTail_LowerTail_ineq_4_16_3
-- name    : FreedmanTail.LowerTail.ineq_4_16_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:15:32.438088+00:00
-- url     : https://prove2.me/theorems/2aa2be8f-2059-4c84-800e-52ed64c997e3
-- title:
--   (4.16:i), i = 3 — η_3 < (1/8) exp[−(1 + δ)k]
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $W\ge0$ a measurable random variable satisfying (4.11a)–(4.11b) for every $\lambda\ge0$, and let $\delta,a,b$ satisfy (4.12a)–(4.12c). With $\lambda=(1+\delta)a/b$, $\varphi(\lambda)=\lambda^2/2-\lambda^3/6$, $k=a^2/b$ and $I_3=(b,2b]$, let $\eta_3=\varphi(\lambda)\int_{I_3}P\{W<x\}e^{-\varphi(\lambda)x}\,dx$. Then
--
--   $$
--   \eta_3<\frac18\exp[-(1+\delta)k].
--   $$
--
--   This bounds the third error term of the proof of Proposition (4.10).
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 110 (PDF p. 11), display (4.16:i), i = 3; proof pp. 111–112

import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
import Definitions.Def_FreedmanTail_LowerTail_Hypotheses
import Definitions.Def_FreedmanTail_LowerTail_ProofNotation
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.16:i) for `i = 3`, p. 110: `η₃ < (1/8) exp[−(1 + δ)k]`. -/
theorem ineq_4_16_3
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    eta P W δ a b (I3 b) < 1 / 8 * Real.exp (-((1 + δ) * kStar a b)) := by sorry

end FreedmanTail.LowerTail
