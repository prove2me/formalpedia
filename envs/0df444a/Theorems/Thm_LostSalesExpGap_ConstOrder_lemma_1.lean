-- Prove2me | Theorems.Thm_LostSalesExpGap_ConstOrder_lemma_1
-- name    : LostSalesExpGap.ConstOrder.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T22:10:26.394927+00:00
-- url     : https://prove2.me/theorems/73430082-101a-49c2-95f2-d98083ac21a6
-- title:
--   Lemma 1, p. 8 — γ(ϱ) is non-decreasing in ϱ = p/h
-- statement:
--   Fix a demand law $\mathcal D$ (nonnegative, finite mean, strictly positive variance). For costs $h,p>0$ let $\gamma$ be the rate of Sec. 2.3, computed from the best constant order $r_\infty$ for $(h,p)$. If $(h_1,p_1)$ and $(h_2,p_2)$ satisfy
--   $$
--   \frac{p_1}{h_1}\le\frac{p_2}{h_2},
--   $$
--   then $\gamma$ at $(h_1,p_1)$ is at most $\gamma$ at $(h_2,p_2)$. Equivalently, writing $\gamma(\varrho)$ for the value of $\gamma$ when $p/h=\varrho$, $\gamma(\varrho)$ is non-decreasing in $\varrho$.
--
--   The lemma says the guaranteed exponential rate is worse when lost sales are expensive relative to holding.
--
--   **Formalization Note** Applied with equal ratios in both directions, the statement also contains the paper's remark (p. 8) that $\gamma$ depends on $(h,p)$ only through $p/h$, which is what makes $\gamma(\varrho)$ well defined. The two parameter records may carry different lead times.
-- source:
--   Xin, Goldberg, Optimality gap of constant-order policies decays exponentially in the lead time for lost sales models, arXiv:1409.1499v2, Lemma 1, p. 8 (proof Sec. 5.2, p. 17)

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LostSalesExpGap.ConstOrder

/-- Lemma 1, p. 8: for a fixed demand law, `γ(ϱ)` is non-decreasing in `ϱ = p/h`: if
`p₁/h₁ ≤ p₂/h₂` then `γ` at `(h₁, p₁)` is at most `γ` at `(h₂, p₂)`. -/
theorem lemma_1 (P : CappedBaseStock.DemandLaw)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P)
    (c₁ c₂ : CappedBaseStock.Parameters) (h₁₂ : c₁.p / c₁.h ≤ c₂.p / c₂.h) :
    gamma P c₁ ≤ gamma P c₂ := by sorry

end LostSalesExpGap.ConstOrder
