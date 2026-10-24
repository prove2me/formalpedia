-- Prove2me | Theorems.Thm_HumanAIComp_Bound_retained_cdf_le
-- name    : HumanAIComp.Bound.retained_cdf_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:51.165847+00:00
-- url     : https://prove2.me/theorems/80e7ed4b-780b-4cef-93ed-01680058fc3c
-- title:
--   Proof of Theorem 1, Appendix K, p. 46 — F_{a+}(t) = max{F_a(t) − ε, 0} ≤ min{F_b(t + δ), 1 − ε} = F_{b−}(t + δ)
-- statement:
--   Let $\mu_a,\mu_b$ be probability measures on $\mathbb R$ with cumulative distribution functions $F_a,F_b$, let $\delta\ge0$, and let $\varepsilon=\sup_{t\in\mathbb R}(F_a(t)-F_b(t+\delta))<1$. Then for every $t\in\mathbb R$,
--   $$
--   F_{a^+}(t)=\max\{F_a(t)-\varepsilon,\,0\}\;\le\;\min\{F_b(t+\delta),\,1-\varepsilon\}=F_{b^-}(t+\delta).
--   $$
--   After normalisation by $1-\varepsilon$ this says that the retained law of $a$ dominates the retained law of $b-\delta$ in the first-order stochastic order, which is the hypothesis of the monotone coupling step.
--
--   Differences from the source:
--   - encoding: the CDFs F_a, F_b of a and b → two probability measures μa, μb on ℝ with F_a = cdf μa, F_b = cdf μb; reason: every probability law on ℝ is the law of a real random variable and conversely; same instances
--   - encoding: ε = sup_{t∈ℝ} (F_a(t) − F_b(t + δ)) → makarovBound δ μa μb = ⨆ t : ℝ, (cdf μa t − cdf μb (t + δ)); reason: the family lies in [−1, 1], so the real iSup is the true supremum; same value
-- source:
--   Baek, Fu, Ma, Peng, AI Agents for Inventory Control: Human-LLM-OR Complementarity, arXiv:2602.12631v2, p. 46, proof of Theorem 1, "By the definition of ε, F_a(t) − ε ≤ F_b(t + δ) for all t, so …"

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_HumanAIComp_Bound_MakarovBound

open MeasureTheory ProbabilityTheory

namespace HumanAIComp.Bound

/-- Proof of Theorem 1, Appendix K, p. 46: with `ε = sup_t (F_a(t) − F_b(t + δ)) < 1`,
`F_{a⁺}(t) = max{F_a(t) − ε, 0} ≤ min{F_b(t + δ), 1 − ε} = F_{b⁻}(t + δ)` for every `t`. -/
theorem retained_cdf_le (μa μb : Measure ℝ) [IsProbabilityMeasure μa] [IsProbabilityMeasure μb]
    (δ : ℝ) (hδ : 0 ≤ δ) (hε : makarovBound δ μa μb < 1) :
    ∀ t : ℝ, max (cdf μa t - makarovBound δ μa μb) 0 ≤
      min (cdf μb (t + δ)) (1 - makarovBound δ μa μb) := by sorry

end HumanAIComp.Bound
