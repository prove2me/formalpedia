-- Prove2me | Theorems.Thm_OnlineConvexOpt_GamesDuality_weak_duality
-- name    : OnlineConvexOpt.GamesDuality.weak_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:21:09.26677+00:00
-- url     : https://prove2.me/theorems/adf11b99-e36b-4351-8a3b-57984e87d27c
-- title:
--   Direction 1 — weak duality (λ_R ≥ λ_C)
-- statement:
--   **Direction 1** of the two-part proof of von Neumann's minimax theorem (Section 8.3,
--   p. 145), also called weak duality in the linear-programming reading of the chapter: for any
--   two-player zero-sum game given by a payoff matrix $A \in \mathbb{R}^{n \times m}$ with
--   $n, m \ge 1$,
--   $$\lambda_C(A) \;\le\; \lambda_R(A),$$
--   where $\lambda_R = \min_{x \in \Delta_n} \max_{y \in \Delta_m} x^{\mathsf T} A y$ is the row
--   player's guaranteed loss and $\lambda_C = \max_{y \in \Delta_m} \min_{x \in \Delta_n}
--   x^{\mathsf T} A y$ is the column player's guaranteed reward. The book's one-line proof is the
--   general max-min $\le$ min-max inequality, specialized at the row player's optimal $x^\star$:
--   $\lambda_R = \max_y (x^\star)^{\mathsf T} A y \ge \max_y \min_x x^{\mathsf T} A y = \lambda_C$.
--
--   **Formalization Note.** No hypothesis bounds the entries of $A$ to $[-1,1]$: the book notes
--   the range is "arbitrary", the argument being invariant to scaling and shifting, and Chapter
--   8's reference item for the harder direction (Theorem 8.3) is also formalized for an
--   unrestricted real matrix.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 145, Direction 1

import Mathlib
import Definitions.Def_OnlineConvexOpt_GamesDuality_Game

namespace OnlineConvexOpt.GamesDuality

/-- **Direction 1** (`λ_R ≥ λ_C`), Hazan, *Introduction to Online Convex Optimization*, 2nd
ed., arXiv:1909.05207v3, p. 145 ("weak duality" in the LP context): for any zero-sum game
given by payoff matrix `A`, the row player's guaranteed loss is at least the column player's
guaranteed reward. -/
theorem weak_duality {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (A : Matrix (Fin n) (Fin m) ℝ) :
    lambdaC A ≤ lambdaR A := by sorry

end OnlineConvexOpt.GamesDuality
