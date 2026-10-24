-- Prove2me | Theorems.Thm_HumanAIComp_Bound_eq_5
-- name    : HumanAIComp.Bound.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:33.369453+00:00
-- url     : https://prove2.me/theorems/8a64e00e-0f39-4255-9d6e-728384fe450a
-- title:
--   (5), proof of Theorem 1, Appendix K, p. 46 — ℙ[b − a > δ] ≥ ℙ[b > t + δ and a ≤ t]
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space (the population) and let $a,b:\Omega\to\mathbb R$ be random variables; in the paper $a=\max(y_H,y_{AI})$ is the better of the human's and the AI's stand-alone performance and $b=y_{H+AI}$ the performance of the human working with the AI, so that $\mathrm{CE}=b-a$ is the individual complementarity effect. Let $\delta\ge 0$. Then for every threshold $t\in\mathbb R$,
--   $$
--   \mathbb P[\,b-a>\delta\,]\;\ge\;\mathbb P[\,b>t+\delta \text{ and } a\le t\,].
--   $$
--   This is the first step of the lower bound in Theorem 1: the event $\{b>t+\delta\}\cap\{a\le t\}$ forces $b-a>\delta$.
--
--   Differences from the source:
--   - generalization: a = max(y_H, y_AI) and b = y_{H+AI} for a person drawn from the population → a, b arbitrary real random variables on an arbitrary probability space (Ω, P); reason: the statement and its proof never use the form of a or b; the paper's a and b are an instance
--   - encoding: random variables a, b, the population probability ℙ, the CDFs F_a, F_b → Measurable a, Measurable b, P.real, ProbabilityTheory.cdf (P.map a), cdf (P.map b); reason: Lean convention; cdf μ t = μ((−∞, t]) is the right-continuous CDF, same instances
-- source:
--   Baek, Fu, Ma, Peng, AI Agents for Inventory Control: Human-LLM-OR Complementarity, arXiv:2602.12631v2, p. 46, proof of Theorem 1, display (5)

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_HumanAIComp_Bound_MakarovBound

open MeasureTheory ProbabilityTheory

namespace HumanAIComp.Bound

/-- Display (5), proof of Theorem 1, Appendix K, p. 46: for every threshold `t`,
`ℙ[b − a > δ] ≥ ℙ[b > t + δ and a ≤ t]`. -/
theorem eq_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : Ω → ℝ) (ha : Measurable a) (hb : Measurable b) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∀ t : ℝ, P.real {ω | t + δ < b ω ∧ a ω ≤ t} ≤ P.real {ω | δ < b ω - a ω} := by sorry

end HumanAIComp.Bound
