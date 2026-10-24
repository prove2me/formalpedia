-- Prove2me | Theorems.Thm_HumanAIComp_Bound_sup_nonneg
-- name    : HumanAIComp.Bound.sup_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:29.910387+00:00
-- url     : https://prove2.me/theorems/6ad5f357-46f5-4381-9028-750752710338
-- title:
--   Proof of Theorem 1, Appendix K, p. 46 — the supremum sup_t (F_a(t) − F_b(t + δ)) is nonnegative (the preceding "yields the bound" is the goal's first clause)
-- statement:
--   Let $\mu_a,\mu_b$ be probability measures on $\mathbb R$ with cumulative distribution functions $F_a,F_b$, and let $\delta\ge 0$. Then
--   $$
--   \varepsilon\;=\;\sup_{t\in\mathbb R}\bigl(F_a(t)-F_b(t+\delta)\bigr)\;\ge\;0 .
--   $$
--   The paper notes this because both CDFs tend to $0$ as $t\to-\infty$. It makes $\varepsilon$ a genuine probability bound and fixes the total mass $1-\varepsilon\le 1$ of the retained sub-distributions in the tightness argument.
--
--   **Formalization Note** The sentence before this one on p. 46 ("Combining (5) and (6) and taking the supremum over $t$ yields the bound") is the first clause of the goal theorem, not of this item.
--
--   Differences from the source:
--   - encoding: the CDFs F_a, F_b of a and b → two probability measures μa, μb on ℝ with F_a = cdf μa, F_b = cdf μb; reason: every probability law on ℝ is the law of a real random variable and conversely; same instances
--   - encoding: ε = sup_{t∈ℝ} (F_a(t) − F_b(t + δ)) → makarovBound δ μa μb = ⨆ t : ℝ, (cdf μa t − cdf μb (t + δ)); reason: the family lies in [−1, 1], so the real iSup is the true supremum; same value
-- source:
--   Baek, Fu, Ma, Peng, AI Agents for Inventory Control: Human-LLM-OR Complementarity, arXiv:2602.12631v2, p. 46, proof of Theorem 1, "The supremum is nonnegative since both CDFs tend to 0 as t → −∞."

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_HumanAIComp_Bound_MakarovBound

open MeasureTheory ProbabilityTheory

namespace HumanAIComp.Bound

/-- Proof of Theorem 1, Appendix K, p. 46: the supremum `sup_t (F_a(t) − F_b(t + δ))` is
nonnegative for any two laws on `ℝ`. -/
theorem sup_nonneg (μa μb : Measure ℝ) [IsProbabilityMeasure μa] [IsProbabilityMeasure μb]
    (δ : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ makarovBound δ μa μb := by sorry

end HumanAIComp.Bound
