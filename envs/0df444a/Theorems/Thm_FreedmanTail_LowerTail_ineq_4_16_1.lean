-- Prove2me | Theorems.Thm_FreedmanTail_LowerTail_ineq_4_16_1
-- name    : FreedmanTail.LowerTail.ineq_4_16_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:14:47.969998+00:00
-- url     : https://prove2.me/theorems/e3c6782e-bdcc-46f7-b548-583ef99ab26f
-- title:
--   (4.16:1) — η_1 < (1/8 − 1/50) exp[−(1 + δ)k]
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $W\ge0$ a measurable random variable satisfying (4.11a)–(4.11b) for every $\lambda\ge0$, and let $\delta,a,b$ satisfy (4.12a)–(4.12c). With $\lambda=(1+\delta)a/b$, $\varphi(\lambda)=\lambda^2/2-\lambda^3/6$, $k=a^2/b$, $N=2/\delta^2$ and $I_1=[0,Na]$, let $\eta_1=\varphi(\lambda)\int_{I_1}P\{W<x\}e^{-\varphi(\lambda)x}\,dx$. Then
--
--   $$
--   \eta_1<\left(\frac18-\frac1{50}\right)\exp[-(1+\delta)k].
--   $$
--
--   This bounds the first error term of the proof of Proposition (4.10).
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 110 (PDF p. 11), display (4.16:1); proof p. 110

import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
import Definitions.Def_FreedmanTail_LowerTail_Hypotheses
import Definitions.Def_FreedmanTail_LowerTail_ProofNotation
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.16:1), p. 110: `η₁ < (1/8 − 1/50) exp[−(1 + δ)k]`. -/
theorem ineq_4_16_1
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    eta P W δ a b (I1 δ a) < (1 / 8 - 1 / 50) * Real.exp (-((1 + δ) * kStar a b)) := by sorry

end FreedmanTail.LowerTail
