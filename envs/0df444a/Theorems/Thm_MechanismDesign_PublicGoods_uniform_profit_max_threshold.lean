-- Prove2me | Theorems.Thm_MechanismDesign_PublicGoods_uniform_profit_max_threshold
-- name    : MechanismDesign.PublicGoods.uniform_profit_max_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T00:21:14.809997+00:00
-- url     : https://prove2.me/theorems/7aa7d6b2-a338-40ab-ab39-ebebc9c86571
-- title:
--   Proposition 3.11 — profit-maximizing threshold $s = 1 + c/2$ in the uniform two-agent example
-- statement:
--   Example 3.3 of Börgers: $N = 2$, both types $\theta_1,\theta_2$ are uniformly distributed on $[0,1]$, and the cost satisfies $0 < c < 2$.
--
--   **Proposition 3.11.** The expected profit maximizing mechanism designer will choose a mechanism with an allocation rule
--   $$q(\theta) = \begin{cases} 1 & \text{if } \theta_1+\theta_2 > s,\\ 0 & \text{otherwise,}\end{cases}\qquad s = 1 + \tfrac12 c .$$
--
--   The monopoly threshold exceeds both the first best threshold $c$ and the utilitarian second best threshold of Proposition 3.10.
--
--   **Formalization Note** Stated as: there exists an incentive-compatible, individually rational mechanism maximizing expected profit among such mechanisms whose decision rule is this threshold rule on all of $\Theta$, and every such profit-maximizing mechanism uses the threshold rule for almost every $\theta$.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.62, Proposition 3.11 (Example 3.3, p.58)

import Mathlib
import Definitions.Def_MechanismDesign_PublicGoods_Model

open MeasureTheory

namespace MechanismDesign.PublicGoods

/-- Börgers, Proposition 3.11 (p.62), Example 3.3 (`N = 2`, types uniform on `[0, 1]`,
`0 < c < 2`): the expected profit maximizing designer chooses the rule "produce iff
`θ_1 + θ_2 > s`" with `s = 1 + c/2`. Stated as: a profit-maximizing mechanism with this rule
exists, and every profit-maximizing mechanism uses this rule for almost every `θ`. -/
theorem uniform_profit_max_threshold (c : ℝ) (hc0 : 0 < c) (hc2 : c < 2) :
    (∃ M : DirectMechanism 2, M.IsProfitMax (uniformExample c hc0) ∧
        ∀ θ ∈ (uniformExample c hc0).typeSpace, M.q θ = thresholdRule (1 + 1 / 2 * c) θ) ∧
    ∀ M : DirectMechanism 2, M.IsProfitMax (uniformExample c hc0) →
      ∀ᵐ θ ∂(uniformExample c hc0).μ, M.q θ = thresholdRule (1 + 1 / 2 * c) θ := by sorry

end MechanismDesign.PublicGoods
