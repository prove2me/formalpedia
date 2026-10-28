-- Prove2me | Theorems.Thm_GreedyRS_Budget_lemma6_greedy_phase_budget
-- name    : GreedyRS.Budget.lemma6_greedy_phase_budget
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:06.200131+00:00
-- url     : https://prove2.me/theorems/6760f6ab-4b68-4918-bcc0-37b2538dc099
-- title:
--   Lemma 6, p. 25 — n_g = C((γ−γ₀)/σ̄; n₀) − n₀ ≤ βe^{−κn₀} with κ = (γ−γ₀)²/(2σ̄²), β = (1−e^{−κ})⁻¹
-- statement:
--   Let $Z_1, Z_2, \dots$ be i.i.d. standard normal, $\bar Z(n)$ their running average, and for a level $x$ and a positive integer $n_0$ let $C(x; n_0) = \mathrm E\big[\inf\{n \ge n_0 : \bar Z(n) < x\}\big] \in [0,\infty]$ be the expected boundary-crossing time (with $\inf\emptyset = \infty$).
--
--   Let $\gamma$ be the gap between the best mean and every other mean and $\bar\sigma > 0$ the bound on the standard deviations (Assumption 1 of the paper), fix $\gamma_0 \in (0, \gamma)$, and let $n_0 \ge 1$ be the number of observations per alternative in the exploration phase of the explore-first greedy procedure. The per-alternative budget of the greedy phase is
--   $$n_g = C\!\left(\frac{\gamma - \gamma_0}{\bar\sigma}; n_0\right) - n_0.$$
--   Set
--   $$\kappa = \frac{(\gamma - \gamma_0)^2}{2\bar\sigma^2}, \qquad \beta = \big(1 - e^{-\kappa}\big)^{-1}.$$
--   Then $\beta > 0$, $\kappa > 0$, and
--   $$n_g \le \beta\, e^{-\kappa n_0}.$$
--
--   The greedy-phase budget therefore decays exponentially as the exploration budget $n_0$ grows: once the total budget per alternative is large, almost all of it can go to the exploration phase, and a very small greedy phase suffices to make the procedure sample optimal and consistent.
--
--   **Formalization Note** The page says "there exist positive constants $\beta$ and $\kappa$" and then names them; the statement uses the named values and asserts their positivity, which is stronger than bare existence. The bound is stated additively, $C\big(\tfrac{\gamma - \gamma_0}{\bar\sigma}; n_0\big) \le n_0 + \beta e^{-\kappa n_0}$, in $[0, \infty]$; since the crossing time is at least $n_0$, this is equivalent to $n_g \le \beta e^{-\kappa n_0}$ and in particular asserts that $C(\cdot; n_0)$ is finite there, and it avoids truncated subtraction. Only the numbers $\gamma, \gamma_0, \bar\sigma$ enter, so Assumption 1 itself is not a hypothesis; $\gamma > 0$ follows from $\gamma_0 \in (0, \gamma)$. The hypothesis $n_0 \ge 1$ is the paper's "positive integer $n_0$" (Lemma 4), under which $C(\cdot; n_0)$ is defined. The paper's display (EC.2.9) writes $C((\gamma - \gamma_0)/\bar\sigma)$ without "$; n_0$"; the statement follows the definition of $n_g$ on p. 25.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 25, Lemma 6 (definition of n_g on p. 25); proof EC.2.4, p. ec9, (EC.2.9)

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GreedyRS.Budget

/-- Lemma 6, p. 25: for `γ0 ∈ (0, γ)`, with `κ = (γ - γ0)² / (2 σ̄²)` and `β = (1 - e^{-κ})⁻¹`,
both constants are positive and the greedy-phase budget `n_g = C((γ - γ0)/σ̄; n0) - n0` satisfies
`n_g ≤ β e^{-κ n0}`, written additively as `C((γ - γ0)/σ̄; n0) ≤ n0 + β e^{-κ n0}`. -/
theorem lemma6_greedy_phase_budget (γ γ0 σbar : ℝ) (hσbar : 0 < σbar) (hγ0 : γ0 ∈ Set.Ioo 0 γ)
    (n0 : ℕ) (hn0 : 1 ≤ n0) :
    let κ := (γ - γ0) ^ 2 / (2 * σbar ^ 2)
    let β := (1 - Real.exp (-κ))⁻¹
    0 < β ∧ 0 < κ ∧
      GreedyRS.Greedy.Cn0 ((γ - γ0) / σbar) n0 ≤ (n0 : ℝ≥0∞) + ENNReal.ofReal (β * Real.exp (-κ * n0)) := by sorry

end GreedyRS.Budget
