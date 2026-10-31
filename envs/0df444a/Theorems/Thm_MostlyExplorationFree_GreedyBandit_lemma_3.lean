-- Prove2me | Theorems.Thm_MostlyExplorationFree_GreedyBandit_lemma_3
-- name    : MostlyExplorationFree.GreedyBandit.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:18.941718+00:00
-- url     : https://prove2.me/theorems/2c8f9f6a-c7a5-46e2-b2b5-5075e7116d8e
-- title:
--   Lemma 3, p. 13 — under Assumptions 1 and 3, every half-space {xᵀu ≥ 0} has context probability at least λ₀/x²_max
-- statement:
--   Let the context law $P_X$ on $\mathbb R^d$ ($d \ge 1$) satisfy the parameter-set assumption ($\|X\|_2 \le x_{\max}$ almost surely, $x_{\max} > 0$) and covariate diversity with constant $\lambda_0 > 0$. Then for every direction $u \in \mathbb R^d$,
--   $$
--   P_X[x^\top u \ge 0] \ge \frac{\lambda_0}{x_{\max}^2}.
--   $$
--
--   Covariate diversity therefore forces every closed half-space through the origin to carry a definite share of the contexts; for the Greedy Bandit this means each arm is chosen with probability bounded below at every step, whatever the current estimates.
--
--   **Formalization Note** Assumption 1 is stated with arm parameters $\beta$ and a bound $b_{\max}$ that play no role here; the lemma holds for any of them. The probability is an extended nonnegative real and $\lambda_0/x_{\max}^2$ is embedded with `ENNReal.ofReal`.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, p. 13, Lemma 3

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Model

open Matrix MeasureTheory ProbabilityTheory

namespace MostlyExplorationFree.GreedyBandit

theorem lemma_3 {d : ℕ} (hd : 1 ≤ d) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (β : Fin 2 → Fin d → ℝ) (xmax bmax lam0 : ℝ)
    (hA1 : ParameterSet μ β xmax bmax) (hA3 : CovariateDiversity μ lam0) (u : Fin d → ℝ) :
    ENNReal.ofReal (lam0 / xmax ^ 2) ≤ μ {x | 0 ≤ x ⬝ᵥ u} := by sorry

end MostlyExplorationFree.GreedyBandit
