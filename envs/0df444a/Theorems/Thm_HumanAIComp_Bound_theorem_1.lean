-- Prove2me | Theorems.Thm_HumanAIComp_Bound_theorem_1
-- name    : HumanAIComp.Bound.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:33.963377+00:00
-- url     : https://prove2.me/theorems/ac9b83a7-953a-457a-ae57-39d04eb0f69e
-- title:
--   Theorem 1, p. 17 — ℙ[CE > δ] ≥ sup_t (F_a(t) − F_b(t + δ)) for every joint law, with equality for some coupling of any two marginals
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a population and $a,b:\Omega\to\mathbb R$ random variables; in the paper $a=\max(y_H,y_{AI})$ is the better of the human's and the AI's stand-alone performance and $b=y_{H+AI}$ the performance of the human working with the AI, so that the individual complementarity effect is $\mathrm{CE}=b-a$. Write $F_a(t)=\mathbb P[a\le t]$ and $F_b(t)=\mathbb P[b\le t]$ for the cumulative distribution functions. Let $\delta\ge0$.
--
--   1. **Lower bound.** For every probability space and every pair of random variables $a,b$,
--   $$
--   \mathbb P[\,b-a>\delta\,]\;\ge\;\sup_{t\in\mathbb R}\bigl(F_a(t)-F_b(t+\delta)\bigr).
--   $$
--   2. **Tightness.** For any two probability laws $\mu_a,\mu_b$ on $\mathbb R$ there is a joint law $\pi$ of $(a,b)$ with marginals $\mu_a$ and $\mu_b$ such that
--   $$
--   \pi[\,b-a>\delta\,]\;=\;\sup_{t\in\mathbb R}\bigl(F_a(t)-F_b(t+\delta)\bigr),\qquad F_a(t)=\mu_a((-\infty,t]),\ F_b(t)=\mu_b((-\infty,t]).
--   $$
--
--   Since each person is observed in only one condition, only the marginal laws of $a$ and $b$ are identified from data; the theorem gives the best lower bound on the fraction of individuals who benefit from collaboration by more than $\delta$ that can be computed from the marginals alone.
--
--   **Formalization Note** The bound is the shared definition `makarovBound`, a real supremum over a family bounded by $1$. The tightness clause quantifies over all probability measures on $\mathbb R$, atoms allowed; a joint law with the given marginals is an element of the published `transferencePlans`.
--
--   Differences from the source:
--   - generalization: a = max(y_H, y_AI) and b = y_{H+AI} for a person drawn from the population → a, b arbitrary real random variables on an arbitrary probability space (Ω, P); reason: the statement and its proof never use the form of a or b; the paper's a and b are an instance
--   - encoding: random variables a, b, the population probability ℙ, the CDFs F_a, F_b → Measurable a, Measurable b, P.real, ProbabilityTheory.cdf (P.map a), cdf (P.map b); reason: Lean convention; cdf μ t = μ((−∞, t]) is the right-continuous CDF, same instances
--   - encoding: ε = sup_{t∈ℝ} (F_a(t) − F_b(t + δ)) → makarovBound δ μa μb = ⨆ t : ℝ, (cdf μa t − cdf μb (t + δ)); reason: the family lies in [−1, 1], so the real iSup is the true supremum; same value
--   - encoding: a joint distribution (coupling) of (a, b) with the given marginals → π ∈ MongeKantorovichYao.transferencePlans μa μb (a probability measure on ℝ × ℝ with π.map Prod.fst = μa, π.map Prod.snd = μb), a = p.1, b = p.2; reason: this is exactly the set of joint laws with those marginals; same instances
--   - encoding: for any marginal distributions of a and b (tightness clause) → for any probability measures μa, μb on ℝ, with F_a = cdf μa, F_b = cdf μb and the joint law on ℝ × ℝ; reason: every probability law on ℝ is the law of a real random variable and conversely; same instances
-- source:
--   Baek, Fu, Ma, Peng, AI Agents for Inventory Control: Human-LLM-OR Complementarity, arXiv:2602.12631v2, p. 17, Theorem 1

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_HumanAIComp_Bound_MakarovBound

open MeasureTheory ProbabilityTheory

namespace HumanAIComp.Bound

/-- Theorem 1 (p. 17). For `δ ≥ 0`: (i) for every population `(Ω, P)` and real random variables
`a, b` on it, `ℙ[b − a > δ] ≥ sup_t (F_a(t) − F_b(t + δ))`; (ii) the bound is tight: for any two
laws `μa, μb` on `ℝ` there is a joint law of `(a, b)` with these marginals under which
`ℙ[b − a > δ]` equals the bound. -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (δ : ℝ) (hδ : 0 ≤ δ) :
    (∀ (P : Measure Ω) [IsProbabilityMeasure P] (a b : Ω → ℝ), Measurable a → Measurable b →
        makarovBound δ (P.map a) (P.map b) ≤ P.real {ω | δ < b ω - a ω}) ∧
    (∀ (μa μb : Measure ℝ) [IsProbabilityMeasure μa] [IsProbabilityMeasure μb],
        ∃ π ∈ MongeKantorovichYao.transferencePlans μa μb,
          π.real {p : ℝ × ℝ | δ < p.2 - p.1} = makarovBound δ μa μb) := by sorry

end HumanAIComp.Bound
