-- Prove2me | Theorems.Thm_KallenbergLP_Games_shapley_stationary_optimal
-- name    : KallenbergLP.Games.shapley_stationary_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:56:49.713053+00:00
-- url     : https://prove2.me/theorems/b7bf556c-9a55-416e-8202-b99677ee7a13
-- title:
--   Theorem 6.2.1 (Shapley) — a contracting stochastic game has stationary optimal policies for both players
-- statement:
--   Let $(E,A,B,p,r)$ be a two-person zero-sum stochastic game with finite state space, finite nonempty action sets $A(i)$, $B(i)$, and substochastic transition probabilities, and suppose Assumption 6.2.1 holds: there are $\mu \gg 0$ and $\alpha \in [0,1)$ with $\sum_j p_{iabj}\mu_j \le \alpha\mu_i$ for all $i$, $a \in A(i)$, $b \in B(i)$. Then there exist stationary policies $(\pi^*)^\infty$ for player I and $(\rho^*)^\infty$ for player II such that
--   $$v(R_1,(\rho^*)^\infty) \le v((\pi^*)^\infty,(\rho^*)^\infty) \le v((\pi^*)^\infty,R_2)$$
--   componentwise, for **all** (history-dependent, randomized) policies $R_1$ of player I and $R_2$ of player II.
--
--   This is Shapley's theorem (1953) for the discounted case $\mu = e$, extended to general $\mu$. It implies that the value of the game exists; Theorem 6.2.2 characterizes it.
--
--   **Formalization Note** The transition probabilities may depend on both players' actions (Assumption 6.2.2 is not assumed). Optimality is against the full class of history-dependent randomized policies.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 192, Theorem 6.2.1 (under Assumption 6.2.1; attributed to Shapley 1953 and Van der Wal & Wessels 1977)

import Mathlib
import Definitions.Def_KallenbergLP_Games_SingleController

namespace KallenbergLP.Games

/-- Theorem 6.2.1 (Shapley 1953; p. 192): under Assumption 6.2.1 there exist stationary optimal
policies for both players. -/
theorem shapley_stationary_optimal {N : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (G : Game N α β) (hA : Assumption621 G) :
    ∃ (π : Fin N → α → ℝ) (ρ : Fin N → β → ℝ) (hπ : IsDecisionRule1 G π)
      (hρ : IsDecisionRule2 G ρ), IsOptimalPair G (stationary1 G π hπ) (stationary2 G ρ hρ) := by sorry

end KallenbergLP.Games
