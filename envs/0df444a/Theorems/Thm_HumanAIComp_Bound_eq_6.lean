-- Prove2me | Theorems.Thm_HumanAIComp_Bound_eq_6
-- name    : HumanAIComp.Bound.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:29.960131+00:00
-- url     : https://prove2.me/theorems/25182cf4-c96d-4aff-b225-6c75a9de2f78
-- title:
--   (6), proof of Theorem 1, Appendix K, p. 46 — Fréchet: ℙ[b > t + δ, a ≤ t] ≥ (1 − F_b(t + δ)) + F_a(t) − 1 = F_a(t) − F_b(t + δ)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $a,b:\Omega\to\mathbb R$ random variables with cumulative distribution functions $F_a(t)=\mathbb P[a\le t]$ and $F_b(t)=\mathbb P[b\le t]$. Let $\delta\ge 0$. Then for every $t\in\mathbb R$,
--   $$
--   \mathbb P[\,b>t+\delta,\ a\le t\,]\;\ge\;\bigl(1-F_b(t+\delta)\bigr)+F_a(t)-1\;=\;F_a(t)-F_b(t+\delta).
--   $$
--   This is the Fréchet inequality $\mathbb P[A\cap B]\ge\mathbb P[A]+\mathbb P[B]-1$ applied to $A=\{b>t+\delta\}$ and $B=\{a\le t\}$. Together with (5) and a supremum over $t$ it gives the lower bound of Theorem 1.
--
--   **Formalization Note** The display is stated as two conjuncts: the inequality with the middle expression, and the identity of the middle and right-hand expressions.
--
--   Differences from the source:
--   - generalization: a = max(y_H, y_AI) and b = y_{H+AI} for a person drawn from the population → a, b arbitrary real random variables on an arbitrary probability space (Ω, P); reason: the statement and its proof never use the form of a or b; the paper's a and b are an instance
--   - encoding: random variables a, b, the population probability ℙ, the CDFs F_a, F_b → Measurable a, Measurable b, P.real, ProbabilityTheory.cdf (P.map a), cdf (P.map b); reason: Lean convention; cdf μ t = μ((−∞, t]) is the right-continuous CDF, same instances
-- source:
--   Baek, Fu, Ma, Peng, AI Agents for Inventory Control: Human-LLM-OR Complementarity, arXiv:2602.12631v2, p. 46, proof of Theorem 1, display (6)

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_HumanAIComp_Bound_MakarovBound

open MeasureTheory ProbabilityTheory

namespace HumanAIComp.Bound

/-- Display (6), proof of Theorem 1, Appendix K, p. 46 (the Fréchet inequality): for every `t`,
`ℙ[b > t + δ, a ≤ t] ≥ (1 − F_b(t + δ)) + F_a(t) − 1 = F_a(t) − F_b(t + δ)`. -/
theorem eq_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : Ω → ℝ) (ha : Measurable a) (hb : Measurable b) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∀ t : ℝ,
      (1 - cdf (P.map b) (t + δ)) + cdf (P.map a) t - 1 ≤ P.real {ω | t + δ < b ω ∧ a ω ≤ t} ∧
      (1 - cdf (P.map b) (t + δ)) + cdf (P.map a) t - 1 = cdf (P.map a) t - cdf (P.map b) (t + δ) := by sorry

end HumanAIComp.Bound
