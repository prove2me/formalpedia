-- Prove2me | Theorems.Thm_MechanismDesign_PublicGoods_uniform_second_best_threshold
-- name    : MechanismDesign.PublicGoods.uniform_second_best_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T00:21:00.495146+00:00
-- url     : https://prove2.me/theorems/7c722978-79c4-4133-82c0-a2ed0440f0f7
-- title:
--   Proposition 3.10 — second best threshold in the uniform two-agent example
-- statement:
--   Example 3.3 of Börgers: $N = 2$, both types $\theta_1,\theta_2$ are uniformly distributed on $[0,1]$, and the cost satisfies $0 < c < 2$.
--
--   **Proposition 3.10.** The utilitarian mechanism designer will choose a mechanism with an allocation rule
--   $$q(\theta) = \begin{cases} 1 & \text{if } \theta_1+\theta_2 > s,\\ 0 & \text{otherwise,}\end{cases}$$
--   where $s$ is determined as follows:
--
--   1. if $c < 2/3$, then $s$ is the unique solution in $[0,1]$ of $-\tfrac23 s^3 + s^2 - \big(1 - \tfrac12 s^2\big)c = 0$;
--   2. if $c \ge 2/3$, then $s = \tfrac12 + \tfrac34 c$.
--
--   The threshold lies strictly above the first best threshold $c$, which measures the inefficiency the budget constraint forces on the designer.
--
--   **Formalization Note** "The utilitarian designer will choose" is stated as three claims: for $c<2/3$ the cubic has exactly one root in $[0,1]$; for the $s$ of case 1 or 2 there exists a second best mechanism (incentive-compatible, individually rational, ex ante budget balanced, welfare-maximizing among such) whose decision rule is the threshold rule on all of $\Theta$; and every second best mechanism uses the threshold rule for almost every $\theta$ (changing $q$ on a null set is harmless).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.61, Proposition 3.10 (Example 3.3, p.58)

import Mathlib
import Definitions.Def_MechanismDesign_PublicGoods_Model

open MeasureTheory

namespace MechanismDesign.PublicGoods

/-- Börgers, Proposition 3.10 (p.61), Example 3.3 (`N = 2`, types uniform on `[0, 1]`,
`0 < c < 2`): the utilitarian (second best) designer chooses the rule "produce iff
`θ_1 + θ_2 > s`", where (i) if `c < 2/3`, `s` is the unique solution in `[0, 1]` of
`−(2/3)s³ + s² − (1 − s²/2)c = 0`, and (ii) if `c ≥ 2/3`, `s = 1/2 + (3/4)c`. Stated as: the
cubic has a unique root in `[0, 1]` when `c < 2/3`; for that `s`, a second best mechanism with
this rule exists, and every second best mechanism uses this rule for almost every `θ`. -/
theorem uniform_second_best_threshold (c : ℝ) (hc0 : 0 < c) (hc2 : c < 2) :
    (c < 2 / 3 →
      ∃! s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧ -(2 / 3) * s ^ 3 + s ^ 2 - (1 - 1 / 2 * s ^ 2) * c = 0) ∧
    ∀ s : ℝ,
      ((c < 2 / 3 ∧ s ∈ Set.Icc (0 : ℝ) 1 ∧
          -(2 / 3) * s ^ 3 + s ^ 2 - (1 - 1 / 2 * s ^ 2) * c = 0) ∨
        (2 / 3 ≤ c ∧ s = 1 / 2 + 3 / 4 * c)) →
      (∃ M : DirectMechanism 2, M.IsSecondBest (uniformExample c hc0) ∧
          ∀ θ ∈ (uniformExample c hc0).typeSpace, M.q θ = thresholdRule s θ) ∧
      ∀ M : DirectMechanism 2, M.IsSecondBest (uniformExample c hc0) →
        ∀ᵐ θ ∂(uniformExample c hc0).μ, M.q θ = thresholdRule s θ := by sorry

end MechanismDesign.PublicGoods
