-- Prove2me | Theorems.Thm_MinimaxRegretRL_Bernstein_total_variance_episode
-- name    : MinimaxRegretRL.Bernstein.total_variance_episode
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:08:48.002931+00:00
-- url     : https://prove2.me/theorems/d5de6e50-dac0-4e65-96a9-dd58e5a21b4b
-- title:
--   Eq. (26) — law of total variance along an episode
-- statement:
--   Fix a deterministic policy $\pi$, a start state $x$ at step $h$, and draw the remaining episode path under the MDP transition law. The expected sum of conditional variances of the next-step values equals the variance of the total remaining reward:
--
--   $$\mathbb E\!\left[\sum_{j=h}^{H}\operatorname{Var}_{Y\sim P(\cdot\mid x_j,\pi(x_j,j))}V_{j+1}^{\pi}(Y)\right]=\operatorname{Var}\!\left(\sum_{j=h}^{H}R(x_j,\pi(x_j,j))\right).$$
--
--   This connects the next-value variances appearing in Bernstein bonuses to the variance of an episode return.
--
--   **Formalization Note** The appendix's Eq. (26) ends both sums at $H-1$ under its shifted terminal convention. Algorithm 2 on p. 4 takes $H$ reward steps and has $V_{H+1}=0$; Lean follows that convention, so both sums include the final step $H$.
-- source:
--   Azar, Osband and Munos, Minimax Regret Bounds for Reinforcement Learning, arXiv:1703.05449v2 (2017), p. 18, Eq. (26); p. 4, Algorithm 2

import Mathlib
import Definitions.Def_MinimaxRegretRL_Bernstein_Path

open scoped Classical

namespace MinimaxRegretRL.Bernstein

/-- Eq. (26), p. 18, translated from the appendix's terminal index H to
Algorithm 2's H reward steps and terminal index H+1. -/
theorem total_variance_episode {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty S] [Nonempty A] (M : MinimaxRegretRL.Hoeffding.MDP S A) (H : ℕ)
    (π : MinimaxRegretRL.Hoeffding.Policy S A H) (h : Fin H) (x : S) :
    pathExp M π h x (pathVarianceSum M π h x) =
      pathVar M π h x (pathReward M π h x) := by sorry

end MinimaxRegretRL.Bernstein
